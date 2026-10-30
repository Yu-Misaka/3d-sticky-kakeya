import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63RichStickyKernel

/-!
# Proposition 6.2 with the terminal witnesses needed by Proposition 6.3

The public re-entry kernel forgets terminal degree and source-normalization
data.  The M9 grain construction needs those fields.  This stronger entry
retains them, and the ordinary public kernel is projected from the same
schedule and its actual terminal calls.
-/

noncomputable section
namespace Kakeya.Assouad

/-- The complete pre-runtime rich kernel used by the two M9 sticky calls. -/
def PureWZ2RichProp62KernelStatement : Prop :=
  ∀ sigma : ℝ, PureWZ2CriticalPackage sigma →
    ∀ outputLoss : ℝ, 0 < outputLoss → outputLoss ≤ 1 →
      Nonempty (PureWZ2.Proposition63RichStickyKernelScheduleData sigma outputLoss)

/-- Closed strengthened Node-3 entry. -/
theorem pure_wz2_node03_rich_prop62_kernel : PureWZ2RichProp62KernelStatement :=
  PureWZ2.proposition63_rich_sticky_kernel

/-- The public Node-3 kernel is a projection of the very same schedules used
by M9.  No second kernel or runtime family is chosen in this adapter. -/
theorem PureWZ2RichProp62KernelStatement.toReentryKernel
    (kernel : PureWZ2RichProp62KernelStatement) :
    PureWZ2PropStickyReentryKernelAt 0 61 := by
  intro sigma critical outputLoss hloss hone
  rcases kernel sigma critical outputLoss hloss hone with ⟨schedule⟩
  exact ⟨{
    sourceLoss := schedule.sourceLoss
    normalizationLoss := schedule.normalizationLoss
    delta₀ := schedule.delta₀
    sourceLoss_pos := schedule.sourceLoss_pos
    normalizationLoss_pos := schedule.normalizationLoss_pos
    sourceLoss_le_half := schedule.sourceLoss_le_half
    normalizationLoss_lt_output := schedule.normalizationLoss_lt_output
    delta₀_pos := schedule.delta₀_pos
    delta₀_le_one := schedule.delta₀_le_one
    run := fun delta hdelta hbound family shading reentry rho hlower hupper => by
      rcases schedule.runTerminal delta hdelta hbound family shading
        reentry rho hlower hupper with ⟨terminal⟩
      exact ⟨terminal.data⟩
    runReentrant := fun delta hdelta hbound family shading reentry
        haxial rho hlower hupper => by
      rcases schedule.runTerminal delta hdelta hbound family shading
        reentry rho hlower hupper with ⟨terminal⟩
      exact ⟨terminal.toReentrant haxial⟩ }⟩

end Kakeya.Assouad
end
