import MyLeanRepo.Kakeya.Assouad.PureWZ2.CommonHeightNormalizedTerminal
import MyLeanRepo.Kakeya.Assouad.PureWZ2.OrdinaryTubeWolffLowerBound

/-! A retained comparison on one common-height ordinary-tube terminal.
This independent lower bound uses ordinary unit-capsule Tube Wolff tests.
The final root uses the length-32 correction in `NormalizedContradiction`. -/

namespace Kakeya.Assouad

theorem pure_wz2_no_critical_package_of_common_height_projection
    (upper : PureWZ2CommonHeightProjectionStatement)
    {sigma : ℝ} (critical : PureWZ2CriticalPackage sigma) : False := by
  obtain ⟨eta, delta₀, heta, hetaEpsilon, hdelta₀, _, lower⟩ :=
    pure_wz2_convex_wolff_lower_bound_in_common_height_chart (sigma / 4)
      (by linarith [critical.sigma_pos])
  have hetaSigma : eta < sigma := by linarith [critical.sigma_pos]
  obtain ⟨delta, hdelta, hdeltaBound, hdeltaOne, ⟨data⟩⟩ :=
    upper sigma critical eta delta₀ heta hetaSigma hdelta₀
  have hlower := lower delta hdelta hdeltaBound data.family
    data.family_nonempty data.bounded_base data.analytic_distinct
    data.vertical_chart data.common_height data.convex_wolff data.shading data.dense
    data.slope_window data.analysisSlope data.analysisSlope_nonsingular
    data.analysisSlope_zero
  have hgap : sigma / 4 < sigma - eta := by linarith [critical.sigma_pos]
  have hstrict : Kakeya.realRpowENN delta (sigma - eta) <
      Kakeya.realRpowENN delta (sigma / 4) := by
    exact (ENNReal.ofReal_lt_ofReal_iff
      (Real.rpow_pos_of_pos hdelta _)).mpr
        (Real.rpow_lt_rpow_of_exponent_gt hdelta hdeltaOne hgap)
  exact (not_le_of_gt hstrict) (hlower.trans data.projection_upper)

theorem pure_wz2_theorem5_2_of_common_height_projection
    (subunit : PureWZ2SubunitPackageStatement)
    (extraction : PureWZ2CriticalExtractionStatement)
    (upper : PureWZ2CommonHeightProjectionStatement) :
    PureWZ2Theorem5_2Statement := by
  by_contra h
  obtain ⟨sigma, ⟨critical⟩⟩ := extraction subunit h
  exact pure_wz2_no_critical_package_of_common_height_projection upper critical

end Kakeya.Assouad
