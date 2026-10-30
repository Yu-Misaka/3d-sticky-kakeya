import MyLeanRepo.Kakeya.Assouad.PureWZ2.PlanarTubeGrid
import MyLeanRepo.Kakeya.Assouad.PureWZ2.CenteredTubeWolff

/-!
# Ordinary geometric properties of the planar grid

The finite grid consists of ordinary unit-segment capsules inside the unit
ball. It satisfies capsule Tube Wolff with an absolute constant and literal
paper essential distinctness, uniformly in the slope offset.
-/

noncomputable section
open MeasureTheory Set
namespace Kakeya.Assouad

theorem planarTubeGrid_axisPoint_mem_segment {n : ℕ} (hn : 0 < n)
    {s : ℝ} (hs : 1 ≤ s) (i : Fin (n * n)) (z : ℝ) (hz : |z| ≤ 1 / 8) :
    slopeOffsetAxisPoint (tubeParamsOfTube ((planarTubeGrid n s).tube i)) z ∈
      Kakeya.unitSegment ((planarTubeGrid n s).tube i).base
        ((planarTubeGrid n s).tube i).direction := by
  rw [planarTubeGrid_params]
  have h := planarTubeGridParams_bounds hn hs (finProdFinEquiv.symm i)
  exact slopeOffsetModelTube_slab_axisPoint_mem_segment _ 0 _ z
    (h.2.2.1.trans (by norm_num)) (h.2.2.2.trans (by norm_num)) (by simpa using hz)

theorem planarTubeGrid_tubeWolff {n : ℕ} (hn : 0 < n)
    {s : ℝ} (hs : 1 ≤ s) : TubeWolffBound (planarTubeGrid n s) 3865470566400 := by
  have h := tubeParameterFrostman_to_centered_tubeWolff (planarTubeGridScale_pos hn)
    (fun i => (planarTubeGrid_lineClass hn hs i).vertical)
    (planarTubeGrid_axisPoint_mem_segment hn hs)
    (by norm_num : (1 : ENNReal) ≤ 150994944)
    (planarTubeGrid_parameter_frostman hn s)
  norm_num at h ⊢
  exact h

theorem planarTubeGrid_in_unitBall {n : ℕ} (hn : 0 < n)
    {s : ℝ} (hs : 1 ≤ s) : (planarTubeGrid n s).IsInUnitBall := by
  intro i q hq
  let p := planarTubeGridParams n s (finProdFinEquiv.symm i)
  let T := (planarTubeGrid n s).tube i
  have hb := planarTubeGridParams_bounds hn hs (finProdFinEquiv.symm i)
  have hmid : ‖slopeOffsetAxisPoint p 0‖ ≤ 1 / 16 := by
    have hnorm := point3_coord_norm_sq (slopeOffsetAxisPoint p 0)
    simp only [slopeOffsetAxisPoint_coord_zero, slopeOffsetAxisPoint_coord_one,
      slopeOffsetAxisPoint_coord_two, mul_zero, add_zero, zero_pow (by decide : 2 ≠ 0),
      add_zero] at hnorm
    have ha : |p.a| ≤ 1 / 64 := hb.1
    have hb' : |p.b| ≤ 1 / 64 := hb.2.1
    nlinarith [sq_abs p.a, sq_abs p.b, abs_le.mp ha, abs_le.mp hb',
      norm_nonneg (slopeOffsetAxisPoint p 0)]
  have hc : IsCompact (Kakeya.unitSegment T.base T.direction) :=
    isCompact_Icc.image (continuous_const.add (continuous_id.smul continuous_const))
  obtain ⟨a, ha, hqa⟩ := exists_dist_le_of_mem_cthickening_closed hc.isClosed
    (planarTubeGridScale_pos hn).le hq
  obtain ⟨t, ht, rfl⟩ := ha
  have ht' : |t - 1 / 2| ≤ 1 / 2 := abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have heq : T.base + t • T.direction =
      slopeOffsetAxisPoint p 0 + (t - 1 / 2) • slopeOffsetUnitDirection p := by
    change slopeOffsetAxisPoint p 0 - (1 / 2 : ℝ) • slopeOffsetUnitDirection p +
      t • slopeOffsetUnitDirection p = _
    module
  have haxis : ‖T.base + t • T.direction‖ ≤ 1 / 16 + 1 / 2 := by
    rw [heq]
    calc
      _ ≤ ‖slopeOffsetAxisPoint p 0‖ + ‖(t - 1 / 2) • slopeOffsetUnitDirection p‖ := norm_add_le _ _
      _ ≤ 1 / 16 + 1 / 2 := by
        simpa only [norm_smul, Real.norm_eq_abs, slopeOffsetUnitDirection_norm, mul_one] using
          add_le_add hmid ht'
  have hnorm : ‖q‖ ≤ 1 := by
    have h := norm_add_le (q - (T.base + t • T.direction)) (T.base + t • T.direction)
    rw [sub_add_cancel] at h
    rw [dist_eq_norm] at hqa
    linarith [planarTubeGridScale_le hn]
  simpa only [Kakeya.DeltaTube.unitBall, Metric.mem_closedBall, dist_zero_right] using hnorm

/-- Centered dilation of an ordinary capsule is inside the dilated full-line tube. -/
theorem wz2PaperCenteredDilatedCarrier_two_subset_axis {delta : ℝ}
    (hdelta : 0 ≤ delta) (T : Kakeya.DeltaTube delta) :
    wz2PaperCenteredDilatedCarrier 2 T ⊆ Metric.cthickening (2 * delta) (tubeAxisLine T) := by
  rintro q ⟨p, hp, rfl⟩
  have hc : IsCompact (Kakeya.unitSegment T.base T.direction) :=
    isCompact_Icc.image (continuous_const.add (continuous_id.smul continuous_const))
  obtain ⟨a, ha, hpa⟩ := exists_dist_le_of_mem_cthickening_closed hc.isClosed hdelta hp
  obtain ⟨t, ht, rfl⟩ := ha
  let b := T.base + (2 * t - 1 / 2) • T.direction
  have hb : b ∈ tubeAxisLine T := ⟨2 * t - 1 / 2, rfl⟩
  apply Metric.mem_cthickening_of_dist_le _ b _ _ hb
  have heq : AffineMap.homothety (wz2PaperTubeMidpoint T) (2 : ℝ) p - b =
      (2 : ℝ) • (p - (T.base + t • T.direction)) := by
    simp only [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add,
      wz2PaperTubeMidpoint, b]
    module
  rw [dist_eq_norm, heq, norm_smul, Real.norm_eq_abs]
  norm_num
  simpa only [dist_eq_norm] using hpa

theorem fin_grid_eq_of_gap_lt {n : ℕ} {d : ℝ} (hd : 0 < d) (i j : Fin n)
    (hgap : |d * (i : ℝ) - d * (j : ℝ)| < d) : i = j := by
  apply Fin.ext
  by_contra hne
  rcases lt_or_gt_of_ne hne with hij | hji
  · have h : (i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast hij
    have hprod := mul_le_mul_of_nonneg_left h hd.le
    have habs := (abs_lt.mp hgap).1
    nlinarith
  · have h : (j : ℝ) + 1 ≤ (i : ℝ) := by exact_mod_cast hji
    have hprod := mul_le_mul_of_nonneg_left h hd.le
    have habs := (abs_lt.mp hgap).2
    nlinarith

theorem planarTubeGrid_eq_of_centered_containment {n : ℕ} (hn : 0 < n)
    {s : ℝ} (hs : 1 ≤ s) (i j : Fin (n * n))
    (hij : ((planarTubeGrid n s).tube i).carrier ⊆
      wz2PaperCenteredDilatedCarrier 2 ((planarTubeGrid n s).tube j)) : i = j := by
  let p := tubeParamsOfTube ((planarTubeGrid n s).tube i)
  let q := tubeParamsOfTube ((planarTubeGrid n s).tube j)
  have hb := planarTubeGridParams_bounds hn hs (finProdFinEquiv.symm j)
  have hc : |q.c| ≤ 1 / 2 := by simpa only [q, planarTubeGrid_params] using hb.2.2.1.trans (by norm_num)
  have hd : |q.d| ≤ 1 / 2 := by simpa only [q, planarTubeGrid_params] using hb.2.2.2.trans (by norm_num)
  have hv : ((planarTubeGrid n s).tube j).direction 2 ≠ 0 := by
    have h := (planarTubeGrid_lineClass hn hs j).vertical
    intro hz
    rw [hz, abs_zero] at h
    norm_num at h
  have hres (z : ℝ) (hz : |z| ≤ 1 / 8) :
      |p.a + p.c * z - (q.a + q.c * z)| ≤ 3 * planarTubeGridScale n := by
    have hpoint : slopeOffsetAxisPoint p z ∈ ((planarTubeGrid n s).tube i).carrier :=
      Metric.mem_cthickening_of_dist_le (slopeOffsetAxisPoint p z)
        (slopeOffsetAxisPoint p z) _ _ (planarTubeGrid_axisPoint_mem_segment hn hs i z hz)
        (by simpa using (planarTubeGridScale_pos hn).le)
    have haxis := wz2PaperCenteredDilatedCarrier_two_subset_axis (planarTubeGridScale_pos hn).le
      ((planarTubeGrid n s).tube j) (hij hpoint)
    have h := (vertical_line_neighbourhood_residual
      (mul_nonneg (by norm_num) (planarTubeGridScale_pos hn).le)
      ((planarTubeGrid n s).tube j) hv hc hd haxis).1
    norm_num at h
    convert h using 1 <;> ring
  have h0 := hres 0 (by norm_num)
  have h1 := hres (1 / 8) (by norm_num)
  simp only [mul_zero, add_zero] at h0
  have hfirst : |p.a - q.a| < planarTubeGridMesh n := by
    have hmesh := planarTubeGridMesh_pos hn
    dsimp only [planarTubeGridScale] at h0
    linarith
  have hsecond : |p.c - q.c| < planarTubeGridMesh n := by
    have hmesh := planarTubeGridMesh_pos hn
    have h0' := abs_le.mp h0
    have h1' := abs_le.mp h1
    dsimp only [planarTubeGridScale] at h0' h1'
    exact abs_lt.mpr ⟨by linarith, by linarith⟩
  simp only [p, q, planarTubeGrid_params, planarTubeGridParams] at hfirst hsecond
  have hfst := fin_grid_eq_of_gap_lt (planarTubeGridMesh_pos hn) _ _ hfirst
  have hsnd := fin_grid_eq_of_gap_lt (planarTubeGridMesh_pos hn) _ _ hsecond
  apply finProdFinEquiv.symm.injective
  exact Prod.ext hfst hsnd

theorem planarTubeGrid_ordinary_distinct {n : ℕ} (hn : 0 < n)
    {s : ℝ} (hs : 1 ≤ s) : WZ2PaperOrdinaryIsEssentiallyDistinct (planarTubeGrid n s) := by
  intro i j hij
  exact ⟨fun h => hij (planarTubeGrid_eq_of_centered_containment hn hs i j h),
    fun h => hij (planarTubeGrid_eq_of_centered_containment hn hs j i h).symm⟩

end Kakeya.Assouad
end
