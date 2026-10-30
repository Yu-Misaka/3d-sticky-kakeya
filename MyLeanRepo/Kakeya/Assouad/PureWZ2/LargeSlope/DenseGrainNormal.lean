import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.LocalSharedNormalCertificate
import MyLeanRepo.Kakeya.Assouad.ConstantAbsorption
import MyLeanRepo.Kakeya.Assouad.WZ1.Corollary26DeltaBudget

/-!
# Local normals on a dense short global grain

A global grain is a thin tube in the rotated y-direction.  On a short
piece with enough volume, the local AD condition and the tube-segment
direction lemma force the local normal to be nearly perpendicular to that
direction.  This certificate uses the supplied configuration itself and
does not require a Proposition 6.2 refinement or a local volume floor for a
three-dimensional coarse cell.
-/

noncomputable section
open MeasureTheory Set
namespace Kakeya.Assouad

/-- A short rectangular part of a global grain, in its own horizontal frame. -/
def pureWZ2ShortGlobalGrain (delta slope x y z : ℝ) : Set Point3 :=
  {p | |pureWZ2HorizontalRotation slope p 0 - x| ≤ 4 * delta ∧
    |pureWZ2HorizontalRotation slope p 1 - y| ≤ Real.sqrt delta / 2 + 2 * delta ∧
    |p 2 - z| ≤ 4 * delta}

theorem pureWZ2ShortGlobalGrain_measurable (delta slope x y z : ℝ) :
    MeasurableSet (pureWZ2ShortGlobalGrain delta slope x y z) := by
  unfold pureWZ2ShortGlobalGrain
  measurability

theorem pureWZ2ShortGlobalGrain_subset_segment
    {delta slope x y z : ℝ}
    (hdelta : 0 < delta) (hsmall : 16 * delta ≤ Real.sqrt delta) :
    pureWZ2ShortGlobalGrain delta slope x y z ⊆
      tubeSegmentCarrier (6 * delta)
        ((pureWZ2HorizontalRotation slope).symm
          (point3 x (y - Real.sqrt delta / 2 - 2 * delta) z))
        (pureWZ2RotatedYAxis slope) 0 (16 * delta) := by
  intro p hp
  let R := pureWZ2HorizontalRotation slope
  let startY := y - Real.sqrt delta / 2 - 2 * delta
  let t := R p 1 - startY
  let base := R.symm (point3 x startY z)
  have hsqrt : Real.sqrt (16 * delta) = 4 * Real.sqrt delta := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 16)]
    norm_num
  have ht : t ∈ Set.Icc 0 (0 + Real.sqrt (16 * delta)) := by
    have hy := abs_le.mp hp.2.1
    dsimp only [t, startY, R]
    rw [hsqrt]
    constructor <;> linarith [Real.sqrt_nonneg delta]
  have haxis : R (base + t • pureWZ2RotatedYAxis slope) =
      point3 x (R p 1) z := by
    change R (R.symm (point3 x startY z) +
      t • R.symm (EuclideanSpace.single (1 : Fin 3) (1 : ℝ))) = _
    simp only [map_add, map_smul,
      LinearIsometryEquiv.apply_symm_apply]
    ext i
    fin_cases i <;> simp [point3, t]
  have hsq : ‖R p - point3 x (R p 1) z‖ ^ 2 ≤ (6 * delta) ^ 2 := by
    rw [point3_coord_norm_sq]
    simp [point3]
    have hx := abs_le.mp hp.1
    have hz := abs_le.mp hp.2.2
    have hrotZ : R p 2 = p 2 := pureWZ2HorizontalRotation_coord_two slope p
    rw [hrotZ]
    nlinarith [sq_nonneg (p 2 - z), sq_nonneg (R p 0 - x)]
  have hdist : dist p (base + t • pureWZ2RotatedYAxis slope) ≤ 6 * delta := by
    rw [← R.dist_map, haxis, dist_eq_norm]
    nlinarith [norm_nonneg (R p - point3 x (R p 1) z)]
  exact Metric.mem_cthickening_of_dist_le p _ _ _
    ⟨t, ht, rfl⟩ hdist

theorem pureWZ2ShortGlobalGrain_dist
    {delta slope x y z : ℝ} {p q : Point3}
    (hdelta : 0 < delta) (hsmall : 16 * delta ≤ Real.sqrt delta)
    (hp : p ∈ pureWZ2ShortGlobalGrain delta slope x y z)
    (hq : q ∈ pureWZ2ShortGlobalGrain delta slope x y z) :
    dist p q ≤ Real.sqrt (16 * delta) := by
  let R := pureWZ2HorizontalRotation slope
  have h0 : |R p 0 - R q 0| ≤ 8 * delta := by
    have h := abs_sub_le (R p 0) x (R q 0)
    rw [abs_sub_comm x] at h
    linarith [hp.1, hq.1]
  have h1 : |R p 1 - R q 1| ≤ Real.sqrt delta + 4 * delta := by
    have h := abs_sub_le (R p 1) y (R q 1)
    rw [abs_sub_comm y] at h
    linarith [hp.2.1, hq.2.1]
  have h2 : |R p 2 - R q 2| ≤ 8 * delta := by
    dsimp only [R]
    rw [pureWZ2HorizontalRotation_coord_two, pureWZ2HorizontalRotation_coord_two]
    have h := abs_sub_le (p 2) z (q 2)
    rw [abs_sub_comm z] at h
    linarith [hp.2.2, hq.2.2]
  have hnorm : ‖R p - R q‖ ≤
      |R p 0 - R q 0| + |R p 1 - R q 1| + |R p 2 - R q 2| := by
    have hsq := point3_coord_norm_sq (R p - R q)
    simp only [PiLp.sub_apply] at hsq
    nlinarith [norm_nonneg (R p - R q), abs_nonneg (R p 0 - R q 0),
      abs_nonneg (R p 1 - R q 1), abs_nonneg (R p 2 - R q 2),
      sq_abs (R p 0 - R q 0), sq_abs (R p 1 - R q 1),
      sq_abs (R p 2 - R q 2)]
  have hsqrt : Real.sqrt (16 * delta) = 4 * Real.sqrt delta := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 16)]
    norm_num
  rw [← R.dist_map, dist_eq_norm, hsqrt]
  linarith

/-- A normal almost perpendicular to a grain's long axis remains nonzero
after projection in any sufficiently close horizontal frame. -/
theorem pureWZ2_frameProjectedNormal_lower_of_long_axis
    {normal : Point3} {slope frameSlope : ℝ}
    (hnormal : ‖normal‖ = 1) (hslope : |slope| ≤ 1)
    (haxis : |inner ℝ (pureWZ2RotatedYAxis slope) normal| ≤ 1 / 4)
    (hframe : |slope - frameSlope| ≤ 1 / 25) :
    (1 / 2 : ℝ) ≤ ‖pureWZ2FrameProjectedNormal frameSlope normal‖ := by
  have hden : pureWZ2HorizontalNorm slope ≤ 3 / 2 := by
    have h := pureWZ2HorizontalNorm_sq slope
    have hslopeSq : slope ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one slope).2 hslope
    nlinarith [pureWZ2HorizontalNorm_pos slope]
  have hdenFrame : 1 ≤ pureWZ2HorizontalNorm frameSlope := by
    have h := pureWZ2HorizontalNorm_sq frameSlope
    nlinarith [sq_nonneg frameSlope, pureWZ2HorizontalNorm_pos frameSlope]
  have hraw : |normal 1 - slope * normal 0| ≤ 3 / 8 := by
    rw [real_inner_comm, pureWZ2HorizontalRotation_inner_y,
      pureWZ2HorizontalRotation_coord_one, abs_div,
      abs_of_pos (pureWZ2HorizontalNorm_pos slope)] at haxis
    have h := (div_le_iff₀ (pureWZ2HorizontalNorm_pos slope)).mp haxis
    have heq : -slope * normal 0 + normal 1 = normal 1 - slope * normal 0 := by ring
    rw [heq] at h
    linarith
  have hcoord : |normal 0| ≤ 1 := by
    simpa [Real.norm_eq_abs, hnormal] using PiLp.norm_apply_le normal (0 : Fin 3)
  have hperturb : |(slope - frameSlope) * normal 0| ≤ 1 / 25 := by
    rw [abs_mul]
    nlinarith [abs_nonneg (slope - frameSlope), abs_nonneg (normal 0)]
  have hrawFrame : |normal 1 - frameSlope * normal 0| ≤ 1 / 2 := by
    have h := abs_add_le (normal 1 - slope * normal 0)
      ((slope - frameSlope) * normal 0)
    have heq : normal 1 - slope * normal 0 +
        (slope - frameSlope) * normal 0 = normal 1 - frameSlope * normal 0 := by ring
    rw [heq] at h
    linarith
  let v := pureWZ2HorizontalRotation frameSlope normal
  have hv : ‖v‖ = 1 := (pureWZ2HorizontalRotation frameSlope).norm_map normal |>.trans hnormal
  have hvy : |v 1| ≤ 1 / 2 := by
    dsimp only [v]
    rw [pureWZ2HorizontalRotation_coord_one, abs_div,
      abs_of_pos (pureWZ2HorizontalNorm_pos frameSlope),
      div_le_iff₀ (pureWZ2HorizontalNorm_pos frameSlope)]
    have heq : -frameSlope * normal 0 + normal 1 = normal 1 - frameSlope * normal 0 := by ring
    rw [heq]
    linarith
  have hsq := point3_coord_norm_sq v
  have hp := norm_xzProjectedNormal_sq v
  rw [hv] at hsq
  have hvySq : (v 1) ^ 2 ≤ 1 / 4 := by
    have h := (sq_le_sq₀ (abs_nonneg (v 1)) (by norm_num : (0 : ℝ) ≤ 1 / 2)).2 hvy
    nlinarith [sq_abs (v 1)]
  rw [pureWZ2FrameProjectedNormal_norm]
  change (1 / 2 : ℝ) ≤ ‖xzProjectedNormal v‖
  nlinarith [norm_nonneg (xzProjectedNormal v)]

/-- Uniform local certificate for every point of any sufficiently dense
short grain in the supplied configuration. -/
theorem pureWZ2_dense_short_global_grain_normal
    (sigma loss eta : ℝ)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (heta : 0 < eta) (hloss : loss < eta) (hgap : 6 * eta < sigma) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
        ∀ cfg : PureWZ2C2GrainConfiguration sigma loss delta,
        ∀ slope x y z : ℝ, |slope| ≤ 1 →
        ∀ E : Set Point3, MeasurableSet E → E ⊆ cfg.shading.union →
          E ⊆ pureWZ2ShortGlobalGrain delta slope x y z →
          ENNReal.ofReal (144 * Real.rpow delta eta * delta ^ 2 * Real.sqrt delta) ≤
            volume E →
          ∀ p : {point : Point3 // point ∈ cfg.shading.union}, p.1 ∈ E →
          ∀ frameSlope : ℝ, |slope - frameSlope| ≤ 1 / 25 →
            (1 / 2 : ℝ) ≤
              ‖pureWZ2FrameProjectedNormal frameSlope (cfg.localGrains.planeMap p)‖ := by
  obtain ⟨dirScale, hdirScale, hdirOne, directionBound⟩ :=
    paper_tube_segment_ad_direction_bound tube_segment_projection_covering_lower_bound
      tube_segment_projection_localization ad_covering_comparison_with_constant
      sigma eta hsigma hsigmaOne heta
  obtain ⟨constantScale, hconstantScale, _, constantBound⟩ :=
    exists_delta_mul_rpow_le_rpow 2 (by norm_num) (show -eta < -loss by linarith)
  have hexponent : 0 < 1 / 2 - 3 * eta / sigma := by
    rw [sub_pos, div_lt_iff₀ hsigma]
    linarith
  obtain ⟨angleScale, hangleScale, _, angleBound⟩ :=
    exists_delta_rpow_le_single (1 / 2 - 3 * eta / sigma) (1 / 16)
      hexponent (by norm_num) (by norm_num)
  let delta₀ := min (1 / 256) (min dirScale (min constantScale angleScale))
  refine ⟨delta₀, by dsimp [delta₀]; positivity,
    (min_le_left _ _).trans (by norm_num), ?_⟩
  intro delta hdelta hcut cfg slope x y z hslope E hE hEcfg hEgrain hmass p hp frameSlope hframe
  have htiny : delta ≤ 1 / 256 := hcut.trans (by simp [delta₀])
  have hdirCut : delta ≤ dirScale := hcut.trans (by simp [delta₀])
  have hconstantCut : delta ≤ constantScale := hcut.trans (by simp [delta₀])
  have hangleCut : delta ≤ angleScale := hcut.trans (by simp [delta₀])
  have hsmall : 16 * delta ≤ Real.sqrt delta := by
    nlinarith [Real.sq_sqrt hdelta.le, Real.sqrt_nonneg delta,
      sq_nonneg (16 * delta - Real.sqrt delta)]
  have hsqrt : Real.sqrt (16 * delta) = 4 * Real.sqrt delta := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 16)]
    norm_num
  have hEball : E ⊆ cfg.shading.union ∩
      Metric.closedBall (p : Point3) (Real.sqrt (16 * delta)) := by
    intro q hq
    exact ⟨hEcfg hq, Metric.mem_closedBall.mpr
      (pureWZ2ShortGlobalGrain_dist hdelta hsmall (hEgrain hq) (hEgrain hp))⟩
  let normal := cfg.localGrains.planeMap p
  have hnormal : ‖normal‖ = 1 := cfg.localGrains.planeMap_unit p
  have hbounded : scalarProjection normal E ⊆ Set.Icc (-4 : ℝ) 4 := by
    rintro value ⟨q, hq, rfl⟩
    obtain ⟨index, hcarrier⟩ := hEcfg hq
    have hbox := (cfg.shading.subset_body index hcarrier).2
    have h0 : |q 0| ≤ 1 := by simpa [Kakeya.Streamlined.axisBox] using hbox.1
    have h1 : |q 1| ≤ 1 := by simpa [Kakeya.Streamlined.axisBox] using hbox.2.1
    have h2 : |q 2| ≤ 1 := by simpa [Kakeya.Streamlined.axisBox] using hbox.2.2
    have hnorm : ‖q‖ ≤ 2 := by
      have h := point3_coord_norm_sq q
      nlinarith [(sq_le_one_iff_abs_le_one (q 0)).2 h0,
        (sq_le_one_iff_abs_le_one (q 1)).2 h1,
        (sq_le_one_iff_abs_le_one (q 2)).2 h2, norm_nonneg q]
    have hinner := abs_real_inner_le_norm q normal
    rw [hnormal, mul_one] at hinner
    exact ⟨by linarith [abs_le.mp (hinner.trans hnorm)],
      by linarith [abs_le.mp (hinner.trans hnorm)]⟩
  have hpaper := (cfg.localGrains.local_ad (16 * delta)
    (by linarith) (by linarith) p).mono (Set.image_mono hEball)
  have hAD : IsADSet1 (scalarProjection normal E) (16 * delta) (1 - sigma)
      (Kakeya.realRpowENN delta (-eta)) := by
    apply (hpaper.toIsADSet1 hbounded).mono_constant
    have h := ENNReal.ofReal_mono (constantBound delta hdelta hconstantCut)
    simpa [Kakeya.realRpowENN, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)] using h
  have hdir := directionBound delta (16 * delta) 0 hdelta hdirCut
    (by linarith) (by linarith)
    ((pureWZ2HorizontalRotation slope).symm
      (point3 x (y - Real.sqrt delta / 2 - 2 * delta) z))
    (pureWZ2RotatedYAxis slope) normal (pureWZ2RotatedYAxis_unit slope) hnormal
    E hE (hEgrain.trans (pureWZ2ShortGlobalGrain_subset_segment hdelta hsmall))
    (by
      rw [hsqrt]
      convert hmass using 1 <;> congr 1 <;> ring) hAD
  have hreal := direction_bound_to_real hdelta (by linarith : 0 < 16 * delta) hdir
  have hpower : Real.sqrt delta * Real.rpow delta (-(3 * eta / sigma)) =
      Real.rpow delta (1 / 2 - 3 * eta / sigma) := by
    rw [Real.sqrt_eq_rpow]
    change delta ^ ((1 : ℝ) / 2) * delta ^ (-(3 * eta / sigma)) =
      delta ^ (1 / 2 - 3 * eta / sigma)
    rw [← Real.rpow_add hdelta]
    congr 1
  have haxis : |inner ℝ (pureWZ2RotatedYAxis slope) normal| ≤ 1 / 4 := by
    rw [hsqrt, mul_assoc, hpower] at hreal
    have h := angleBound delta hdelta hangleCut
    linarith
  exact pureWZ2_frameProjectedNormal_lower_of_long_axis hnormal hslope haxis hframe

end Kakeya.Assouad
end
