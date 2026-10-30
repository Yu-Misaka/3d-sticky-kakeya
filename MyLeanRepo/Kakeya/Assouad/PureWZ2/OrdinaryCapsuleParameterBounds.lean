import MyLeanRepo.Kakeya.Assouad.PureWZ2.OrdinaryCapsuleMidpoint

/-! Quantitative necessary conditions for two fine tubes to fit into one
ordinary coarse capsule. The separate midpoint bound retains the fifth
coordinate which is lost by the four supporting-line parameters. -/

noncomputable section
open MeasureTheory Set
namespace Kakeya.Assouad

theorem ordinary_capsule_pair_parameter_bounds
    {delta r : ℝ} (hdelta : 0 ≤ delta) (hr : 0 ≤ r) (hrSmall : r ≤ 1 / 8)
    (S U : Kakeya.DeltaTube delta) (T : Kakeya.DeltaTube r)
    (hS : (1 / 2 : ℝ) ≤ |S.direction 2|)
    (hsegmentS : ∀ z, |z| ≤ 1 / 8 → slopeOffsetAxisPoint (tubeParamsOfTube S) z ∈
      Kakeya.unitSegment S.base S.direction)
    (hsegmentU : ∀ z, |z| ≤ 1 / 8 → slopeOffsetAxisPoint (tubeParamsOfTube U) z ∈
      Kakeya.unitSegment U.base U.direction)
    (hST : S.carrier ⊆ T.carrier) (hUT : U.carrier ⊆ T.carrier) :
    |(tubeParamsOfTube S).a - (tubeParamsOfTube U).a| ≤ 160 * r ∧
    |(tubeParamsOfTube S).b - (tubeParamsOfTube U).b| ≤ 160 * r ∧
    |(tubeParamsOfTube S).c - (tubeParamsOfTube U).c| ≤ 160 * r ∧
    |(tubeParamsOfTube S).d - (tubeParamsOfTube U).d| ≤ 160 * r := by
  have hvBound := capsule_container_vertical hdelta hr hrSmall S T hS hST
  have hv : T.direction 2 ≠ 0 := by intro hz; rw [hz, abs_zero] at hvBound; linarith
  have hslopes : |(tubeParamsOfTube T).c| ≤ 4 ∧ |(tubeParamsOfTube T).d| ≤ 4 := by
    have hden : 0 < |T.direction 2| := by linarith
    have hcoord (j : Fin 3) : |T.direction j| ≤ 1 := by
      simpa only [T.direction_unit, Real.norm_eq_abs] using PiLp.norm_apply_le T.direction j
    constructor
    · change |T.direction 0 / T.direction 2| ≤ 4
      rw [abs_div]
      exact (div_le_iff₀ hden).2 (by linarith [hcoord 0])
    · change |T.direction 1 / T.direction 2| ≤ 4
      rw [abs_div]
      exact (div_le_iff₀ hden).2 (by linarith [hcoord 1])
  have hres (V : Kakeya.DeltaTube delta)
      (hsegment : ∀ z, |z| ≤ 1 / 8 → slopeOffsetAxisPoint (tubeParamsOfTube V) z ∈
        Kakeya.unitSegment V.base V.direction)
      (hVT : V.carrier ⊆ T.carrier) (z : ℝ) (hz : |z| ≤ 1 / 8) :
      |(tubeParamsOfTube V).a + (tubeParamsOfTube V).c * z -
        ((tubeParamsOfTube T).a + (tubeParamsOfTube T).c * z)| ≤ 5 * r ∧
      |(tubeParamsOfTube V).b + (tubeParamsOfTube V).d * z -
        ((tubeParamsOfTube T).b + (tubeParamsOfTube T).d * z)| ≤ 5 * r := by
    have hpoint := hVT (Metric.mem_cthickening_of_dist_le
      (slopeOffsetAxisPoint (tubeParamsOfTube V) z)
      (slopeOffsetAxisPoint (tubeParamsOfTube V) z) _ _
      (hsegment z hz) (by simpa using hdelta))
    have haxis : slopeOffsetAxisPoint (tubeParamsOfTube V) z ∈
        Metric.cthickening r (tubeAxisLine T) := by
      apply Metric.cthickening_subset_of_subset r _ hpoint
      rintro q ⟨t, ht, rfl⟩
      exact ⟨t, rfl⟩
    have h := vertical_line_neighbourhood_residual hr T hv hslopes.1 hslopes.2 haxis
    norm_num at h
    exact h
  have h0 := hres S hsegmentS hST 0 (by norm_num)
  have h1 := hres S hsegmentS hST (1 / 8) (by norm_num)
  have hu0 := hres U hsegmentU hUT 0 (by norm_num)
  have hu1 := hres U hsegmentU hUT (1 / 8) (by norm_num)
  simp only [mul_zero, add_zero] at h0 hu0
  exact ⟨abs_le.mpr ⟨by linarith [abs_le.mp h0.1, abs_le.mp hu0.1],
      by linarith [abs_le.mp h0.1, abs_le.mp hu0.1]⟩,
    abs_le.mpr ⟨by linarith [abs_le.mp h0.2, abs_le.mp hu0.2],
      by linarith [abs_le.mp h0.2, abs_le.mp hu0.2]⟩,
    abs_le.mpr ⟨by linarith [abs_le.mp h0.1, abs_le.mp hu0.1, abs_le.mp h1.1, abs_le.mp hu1.1],
      by linarith [abs_le.mp h0.1, abs_le.mp hu0.1, abs_le.mp h1.1, abs_le.mp hu1.1]⟩,
    abs_le.mpr ⟨by linarith [abs_le.mp h0.2, abs_le.mp hu0.2, abs_le.mp h1.2, abs_le.mp hu1.2],
      by linarith [abs_le.mp h0.2, abs_le.mp hu0.2, abs_le.mp h1.2, abs_le.mp hu1.2]⟩⟩

end Kakeya.Assouad
end
