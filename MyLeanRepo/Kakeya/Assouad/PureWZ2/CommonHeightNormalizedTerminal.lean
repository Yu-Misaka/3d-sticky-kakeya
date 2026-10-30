import MyLeanRepo.Kakeya.Assouad.PureWZ2.NormalizedTerminal
import MyLeanRepo.Kakeya.Assouad.PureWZ2.CommonHeightTubeWolff

/-! The actual terminal additionally retains the common-height unit segments.
The historical normalized interfaces are obtained by forgetting this witness. -/

noncomputable section
namespace Kakeya.Assouad

structure PureWZ2CommonHeightProjectionData (sigma loss delta : ℝ)
    extends PureWZ2NormalizedProjectionData sigma loss delta where
  common_height : HasCommonHeightTubeModel family

def PureWZ2CommonHeightProjectionStatement : Prop :=
  ∀ sigma : ℝ, PureWZ2CriticalPackage sigma →
    ∀ loss scaleCeiling : ℝ, 0 < loss → loss < sigma → 0 < scaleCeiling →
      ∃ delta : ℝ, 0 < delta ∧ delta ≤ scaleCeiling ∧ delta < 1 ∧
        Nonempty (PureWZ2CommonHeightProjectionData sigma loss delta)

theorem PureWZ2CommonHeightProjectionStatement.toNormalized
    (h : PureWZ2CommonHeightProjectionStatement) : PureWZ2NormalizedProjectionStatement := by
  intro sigma critical loss scaleCeiling hloss hsigma hscale
  obtain ⟨delta, hd, hdc, hd1, ⟨data⟩⟩ := h sigma critical loss scaleCeiling hloss hsigma hscale
  exact ⟨delta, hd, hdc, hd1, ⟨data.toPureWZ2NormalizedProjectionData⟩⟩

end Kakeya.Assouad
end
