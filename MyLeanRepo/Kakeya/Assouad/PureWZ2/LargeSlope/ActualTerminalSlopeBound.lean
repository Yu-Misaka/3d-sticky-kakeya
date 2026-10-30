import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.DirectHalfOffsetTerminalFinalVolume
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.FinalQuotientLossSchedule

/-!
# A pre-runtime slope-offset bound for the actual Node-6 terminal

The source-power estimate for `safePublicSlope` and the source-to-target
radius estimate are combined before requesting the retained construction.
The resulting cutoff is independent of its eventual family and slope.
-/

noncomputable section
namespace Kakeya.Assouad

open PureWZ2DirectCommonYSourceAssembly
open PureWZ2DirectCommonYSourceAssembly.TerminalGeometry

theorem exists_actual_terminal_slope_offset_cutoff
    (loss epsilon : ℝ) (hloss : 0 < loss) (hepsilon : 0 < epsilon)
    (hgap : 2 * epsilon < (1 - 2 * epsilon) * loss) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ {logExponent : ℕ} {sigma delta : ℝ}
        (source : PureWZ2DirectCommonYSourceAssembly logExponent sigma epsilon delta)
        (terminal : source.TerminalGeometry),
        0 < delta → delta ≤ delta₀ →
        1 + |safePublicSlope source terminal 0| ≤
          Real.rpow terminal.targetDelta (-loss) := by
  obtain ⟨scaleCutoff, hscalePos, hscaleOne, hscale⟩ :=
    exists_delta_for_halfOffsetLineClassTargetDelta_power_upper epsilon hepsilon
  obtain ⟨slopeCutoff, hslopePos, hslopeOne, hslope⟩ :=
    exists_delta_constant_mul_power_le_power
      (ENNReal.ofReal finalVolumeSlopeSourceCoefficient) ENNReal.ofReal_ne_top
      (-((1 - 2 * epsilon) * loss)) (-(2 * epsilon)) (by linarith)
  refine ⟨min scaleCutoff slopeCutoff, lt_min hscalePos hslopePos,
    (min_le_left _ _).trans hscaleOne, ?_⟩
  intro logExponent sigma delta source terminal hdelta hcutoff
  have htarget := hscale source hdelta (hcutoff.trans (min_le_left _ _))
  have hsource := two_mul_one_add_finiteSlicePublicSlopeBound_le_source_power
    source terminal hepsilon
  have hbound := hslope hdelta (hcutoff.trans (min_le_right _ _))
  have hreal : finalVolumeSlopeSourceCoefficient * Real.rpow delta (-(2 * epsilon)) ≤
      Real.rpow delta (-((1 - 2 * epsilon) * loss)) := by
    rw [Kakeya.realRpowENN, Kakeya.realRpowENN,
      ← ENNReal.ofReal_mul finalVolumeSlopeSourceCoefficient_pos.le] at hbound
    exact (ENNReal.ofReal_le_ofReal_iff (Real.rpow_nonneg hdelta.le _)).mp hbound
  calc
    1 + |safePublicSlope source terminal 0| ≤
        2 * (1 + finiteSlicePublicSlopeBound source terminal) := by
      unfold finiteSlicePublicSlopeBound
      linarith [abs_nonneg (safePublicSlope source terminal 0)]
    _ ≤ finalVolumeSlopeSourceCoefficient * Real.rpow delta (-(2 * epsilon)) := hsource
    _ ≤ Real.rpow delta (-((1 - 2 * epsilon) * loss)) := hreal
    _ = Real.rpow (Real.rpow delta (1 - 2 * epsilon)) (-loss) := by
      calc
        _ = Real.rpow delta ((1 - 2 * epsilon) * (-loss)) := by congr 1; ring
        _ = _ := Real.rpow_mul hdelta.le _ _
    _ ≤ Real.rpow terminal.targetDelta (-loss) :=
      Real.rpow_le_rpow_of_nonpos source.halfOffsetLineClassTargetDelta_pos
        htarget (by linarith)

/-- The final-quotient loss schedule leaves more than enough room for the
actual terminal's offset. -/
theorem exists_actual_terminal_slope_offset_cutoff_for_output_loss
    (loss : ℝ) (hloss : 0 < loss) (hlossOne : loss ≤ 1) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ {logExponent : ℕ} {sigma delta : ℝ}
        (source : PureWZ2DirectCommonYSourceAssembly
          logExponent sigma (pureWZ2FinalEpsilon loss) delta)
        (terminal : source.TerminalGeometry),
        0 < delta → delta ≤ delta₀ →
        1 + |safePublicSlope source terminal 0| ≤
          Real.rpow terminal.targetDelta (-loss) := by
  have heq : pureWZ2FinalEpsilon loss = loss / 16000 := by
    unfold pureWZ2FinalEpsilon pureWZ2FinalNearbyLoss
    rw [min_eq_left (by linarith : loss / 16 ≤ (1 : ℝ) / 4)]
    ring
  apply exists_actual_terminal_slope_offset_cutoff loss (pureWZ2FinalEpsilon loss) hloss
  · rw [heq]
    positivity
  · rw [heq]
    nlinarith [mul_pos hloss (by linarith : 0 < 7999 - loss)]

end Kakeya.Assouad
end
