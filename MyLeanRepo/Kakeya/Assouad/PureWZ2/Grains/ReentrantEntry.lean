import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.PureHierarchyInitialReentrantSourceProducer
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.ADBridge

/-!
# Proposition 6.3 with the witnesses needed by Proposition 6.4

The M9 construction already proves substantially more than the existential
paper statement.  This entry retains its grains and ordinary/cropped re-entry
on the same shading.  The paper conclusion below is a projection of that
construction, with only monotone weakening of the loss.
-/

noncomputable section
namespace Kakeya.Assouad

/-- The constructive Proposition 6.3 output used by the C2 hierarchy.  The
caller chooses the loss ceiling and scale ceiling before the configuration. -/
def PureWZ2ReentrantGrainsStatement
    (capability : PureWZ2PropStickyCapability) : Prop :=
  ∀ sigma : ℝ, PureWZ2CriticalPackage sigma →
    PureWZ2HierarchyInitialReentrantSourceAt capability sigma

/-- Proposition 6.3 as a consumer of the rich Node-3 mathematical output.
The supplied terminal kernels choose both M9 sticky calls and their actual
coarse/fine witnesses; they are not used just for a numerical exponent. -/
theorem pure_wz2_node04_reentrant_grains_from_prop62
    (kernel : PureWZ2RichProp62KernelStatement)
    (capability : PureWZ2PropStickyCapability) :
    PureWZ2ReentrantGrainsStatement capability := by
  intro sigma critical
  exact pureWZ2_hierarchy_initial_reentrant_source_production_with_kernel
    kernel capability critical

/-- A completed Proposition 6.3 entry retaining both the analytic grains and
the exact re-entry certificate constructed by the M9 proof. -/
theorem pure_wz2_node04_reentrant_grains
    (capability : PureWZ2PropStickyCapability) :
    PureWZ2ReentrantGrainsStatement capability :=
  pure_wz2_node04_reentrant_grains_from_prop62
    pure_wz2_node03_rich_prop62_kernel capability

/-- Recover precisely the existing paper statement from the retained source.
The family, shading, slope, and plane map are unchanged by this projection. -/
theorem PureWZ2ReentrantGrainsStatement.toGrainsFromCritical
    {capability : PureWZ2PropStickyCapability}
    (grains : PureWZ2ReentrantGrainsStatement capability) :
    PureWZ2GrainsFromCriticalStatement := by
  intro sigma critical outputLoss delta₀ hloss hdelta₀
  rcases grains sigma critical outputLoss delta₀ hloss hdelta₀ with
    ⟨sourceLoss, delta, hsourceLoss, hsourceOutput, hdelta, hdeltaBound,
      ⟨source⟩⟩
  exact ⟨delta, hdelta, hdeltaBound,
    ⟨source.grain.grain.mono_loss hdelta source.grain.extremal.delta_le_one
      hsourceLoss.le hsourceOutput.le⟩⟩

end Kakeya.Assouad
end
