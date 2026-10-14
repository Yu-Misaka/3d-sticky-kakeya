/- Appended to the non-`module` audit driver so imported private proof bodies
   are available. This inspects kernel declarations, not source imports. -/
open Lean Elab Command

namespace BlueprintDependencies

def kind : ConstantInfo → String
  | .thmInfo _ => "theorem"
  | .defnInfo _ => "definition"
  | .inductInfo _ => "inductive"
  | .axiomInfo _ => "axiom"
  | .opaqueInfo _ => "opaque"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"
  | .quotInfo _ => "quotient"

/-- Include the structure named by a kernel projection, not just `.const` nodes. -/
def references (e : Expr) : IO (Array Name) := do
  let names ← IO.mkRef ({} : NameHashSet)
  e.forEach fun subterm => do
    match subterm with
    | .const name _ | .proj name _ _ => names.modify (·.insert name)
    | _ => pure ()
  return (← names.get).toArray.qsort Name.lt

def structuralReferences : ConstantInfo → IO (Array Name)
  | .inductInfo value => pure value.ctors.toArray
  | .ctorInfo value => pure #[value.induct]
  | .recInfo value => do
      let mut names := value.all.toArray
      for rule in value.rules do
        names := names ++ #[rule.ctor] ++ (← references rule.rhs)
      return names
  | _ => pure #[]

/-- Emit the complete project-local closure, with library declarations as a
    boundary. Each edge records whether it comes from a type, value or the
    kernel data for an inductive declaration/recursor. Cycles are visited once. -/
def collect (root : Name) (projectRoots : Array Name) (output : System.FilePath)
    (visibleLibrary : Array Name := #[]) :
    CommandElabM Unit := do
  let env := (← getEnv).setExporting false
  let kernel := env.checked.get
  let projectModules := env.header.moduleNames.map fun name =>
    projectRoots.any (·.isPrefixOf name)
  let project := fun name => match env.getModuleIdxFor? name with
    | some idx => projectModules[idx]!
    | none => projectRoots.any (·.isPrefixOf env.mainModule)
  let selected := fun name => project name || visibleLibrary.contains name
  unless project root do throwError "Dependency root is outside the project: {root}"
  let handle ← IO.FS.Handle.mk output .write
  handle.putStrLn (Json.mkObj [
    ("root", toJson root.toString),
    ("module_roots", toJson (projectRoots.map Name.toString))]).compress
  let mut queue := #[root]
  let mut seen := ({} : NameHashSet).insert root
  let mut boundary : NameHashSet := {}
  let mut index := 0
  while index < queue.size do
    let name := queue[index]!
    index := index + 1
    let some info := kernel.find? name
      | throwError "Missing kernel declaration in dependency closure: {name}"
    -- Explicitly linked library declarations are terminal nodes. Their
    -- incoming kernel references are retained without traversing all Mathlib.
    let types ← if project name then references info.type else pure #[]
    let values ← match if project name then info.value? (allowOpaque := true) else none with
      | some value => references value
      | none => pure #[]
    let structural ← if project name then structuralReferences info else pure #[]
    for dependency in types ++ values ++ structural do
      unless (kernel.find? dependency).isSome do
        throwError "Missing referenced kernel declaration: {name} → {dependency}"
      if selected dependency then
        if !seen.contains dependency then
          seen := seen.insert dependency
          queue := queue.push dependency
      if !project dependency then
        boundary := boundary.insert dependency
    let range ← findDeclarationRanges? name
    let moduleName := (env.getModuleIdxFor? name).map
      (fun idx => env.header.moduleNames[idx]!) |>.getD env.mainModule
    let jsonNames := fun names => toJson ((names.filter selected).map Name.toString)
    handle.putStrLn (Json.mkObj [
      ("name", toJson name.toString), ("module", toJson moduleName.toString),
      ("kind", toJson (kind info)),
      ("scope", toJson (if project name then "project" else "library")),
      ("line", toJson (range.map (·.selectionRange.pos.line))),
      ("type", jsonNames types), ("value", jsonNames values),
      ("structural", jsonNames structural)]).compress
    if index % 5000 == 0 then
      liftIO <| IO.println s!"Lean dependencies: {index} declarations inspected"
      (← IO.getStdout).flush
  handle.putStrLn (Json.mkObj [
    ("boundary", toJson (boundary.toArray.qsort Name.lt |>.map Name.toString))]).compress
  handle.flush
  liftIO <| IO.println s!"Lean dependencies: {seen.size} inspected declarations (project and selected library leaves), {boundary.size} library references"

end BlueprintDependencies
