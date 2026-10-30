import MyLeanRepo.Kakeya.Assouad.PureWZ2.Node7AffineScalarSchedule
import MyLeanRepo.Kakeya.Assouad.Targets.PureWZ2Node06LargeSlope
import MyLeanRepo.Kakeya.Assouad.PureWZ2.PaperTerminalNormalization
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.ActualTerminalSlopeBound

/-!
# Node 7b: preparation from the retained Proposition 6.5 construction

All normalization and source-slope cutoffs are fixed first.  Node 6 is then
called once.  Its literal final family, shading, public slope, CWA and
projection upper bound are transported by the proved slope-offset map and
slab restriction, followed by analytic cleanup.  The retained common source
is used only to bound the magnitude of that actual public slope.
-/

noncomputable section

open MeasureTheory Set

namespace Kakeya.Assouad

/-- Normalize the actual returned large-slope terminal.  This theorem takes the
strong Node-6 result as its only upstream proof input. -/
theorem pure_wz2_node7b_common_height_from_retained_large_slope
    (largeSlope : PureWZ2LargeSlopeRetainedStatement) :
    PureWZ2CommonHeightProjectionStatement := by
  intro sigma critical analyticLoss scaleCeiling
    hanalyticPos hanalyticSigma hscaleCeiling
  obtain ⟨normalization⟩ := pure_wz2_paper_terminal_normalization_cutoff
      sigma analyticLoss critical.sigma_pos critical.sigma_lt_one
      hanalyticPos hanalyticSigma
  let largeLoss : ℝ := analyticLoss / 10000
  have hlargeLoss : 0 < largeLoss := by dsimp only [largeLoss]; positivity
  have hlargeLossOne : largeLoss ≤ 1 := by
    dsimp only [largeLoss]
    linarith [hanalyticSigma, critical.sigma_lt_one]
  obtain ⟨sourceCutoff, hsourceCutoff, _hsourceCutoffOne, hslopeBound⟩ :=
    exists_actual_terminal_slope_offset_cutoff_for_output_loss
      largeLoss hlargeLoss hlargeLossOne
  let targetCeiling : ℝ := min (scaleCeiling / 12) normalization.delta₀
  have htargetCeiling : 0 < targetCeiling :=
    lt_min (by positivity) normalization.delta₀_pos
  rcases largeSlope sigma critical largeLoss targetCeiling sourceCutoff
      hlargeLoss htargetCeiling hsourceCutoff with
    ⟨logExponent, sourceDelta, hsourceDelta, hsourceDeltaBound,
      node6, terminalBound⟩
  have hnormalization : node6.terminal.targetDelta ≤ normalization.delta₀ :=
    terminalBound.trans (min_le_right _ _)
  obtain ⟨refined⟩ := normalization.run node6.toLargeSlopeConfiguration
    hnormalization
    (hslopeBound node6.commonSource node6.terminal hsourceDelta hsourceDeltaBound)
  have hfinalScale : 12 * node6.terminal.targetDelta ≤ scaleCeiling := by
    have h := terminalBound.trans (min_le_left _ _)
    linarith
  have hfinalLtOne : 12 * node6.terminal.targetDelta < 1 := by
    linarith [normalization.radius_small]
  let output : PureWZ2CommonHeightProjectionData sigma analyticLoss
      (12 * node6.terminal.targetDelta) :=
    { toPureWZ2NormalizedProjectionData := refined.configuration
      common_height := refined.common_height }
  exact ⟨12 * node6.terminal.targetDelta, by positivity [node6.terminalData.delta_pos],
    hfinalScale, hfinalLtOne, ⟨output⟩⟩

/-- Preserve the historical normalized output by forgetting the extra
common-height witness on the same returned configuration. -/
theorem pure_wz2_node7b_normalized_from_retained_large_slope
    (largeSlope : PureWZ2LargeSlopeRetainedStatement) :
    PureWZ2NormalizedProjectionStatement :=
  (pure_wz2_node7b_common_height_from_retained_large_slope largeSlope).toNormalized

/-- Preserve the old preparation statement using the same terminal. -/
theorem pure_wz2_node7b_from_retained_large_slope
    (largeSlope : PureWZ2LargeSlopeRetainedStatement) :
    PureWZ2ParameterFrostmanPreparationStatement :=
  (pure_wz2_node7b_normalized_from_retained_large_slope largeSlope).toPreparation

/-- Compatibility with the historical Node-7 signature.  Its old erased
large-slope input cannot recover a common-y source; the stronger proved Node-6
entry supplies that source, and is consumed by the theorem above. -/
theorem pure_wz2_node7b_preparation
    (h_subunit : PureWZ2SubunitPackageStatement)
    (h_critical : PureWZ2CriticalExtractionStatement)
    (h_propsticky : PureWZ2PropStickyStatement)
    (h_grains : PureWZ2GrainsStatement)
    (h_c2grains : PureWZ2C2GrainsStatement)
    (_h_largeslope : PureWZ2LargeSlopeStatement) :
    PureWZ2ParameterFrostmanPreparationStatement :=
  pure_wz2_node7b_from_retained_large_slope
    (pure_wz2_node06_large_slope_retained
      (h_c2grains h_subunit h_critical h_propsticky h_grains))

end Kakeya.Assouad

end
