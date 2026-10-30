import MyLeanRepo.Kakeya.Assouad.PureWZ2.LongitudinalTubeGrid

/-! Unit-ball support and the normalized twisted projection of the
longitudinal grid. No Tube Wolff or CWA count is assumed here. -/

noncomputable section
open MeasureTheory Set
namespace Kakeya.Assouad

theorem longitudinalTubeGrid_in_unitBall {n : ℕ} (hn : 0 < n) :
    (longitudinalTubeGrid n).IsInUnitBall := by
  intro i q hq
  let k := (Fintype.equivFin (LongitudinalTubeGridIndex n)).symm i
  let p := longitudinalTubeGridParams n k
  let m := longitudinalTubeGridCenter n k
  let T := (longitudinalTubeGrid n).tube i
  have hp := longitudinalTubeGridParams_bounds hn k
  have hm := longitudinalTubeGrid_center_bounds hn k
  have hcoordinate (a c : ℝ) (ha : |a| ≤ 1 / 64) (hc : |c| ≤ 1 / 64) :
      |a + c * m| ≤ 1 / 16 := by
    calc
      _ ≤ |a| + |c| * |m| := by simpa only [abs_mul] using abs_add_le a (c*m)
      _ ≤ (1 / 64 : ℝ) + (1 / 64) * (1 / 64) := by gcongr
      _ ≤ _ := by norm_num
  have hx := hcoordinate p.a p.c hp.1 hp.2.2.1
  have hy := hcoordinate p.b p.d hp.2.1 hp.2.2.2
  have hmid : ‖slopeOffsetAxisPoint p m‖ ≤ 1 / 8 := by
    have hnorm := point3_coord_norm_sq (slopeOffsetAxisPoint p m)
    simp only [slopeOffsetAxisPoint_coord_zero, slopeOffsetAxisPoint_coord_one,
      slopeOffsetAxisPoint_coord_two] at hnorm
    have hm' : |m| ≤ 1 / 64 := hm
    nlinarith [sq_abs (p.a + p.c*m), sq_abs (p.b+p.d*m), sq_abs m,
      abs_le.mp hx, abs_le.mp hy, abs_le.mp hm', norm_nonneg (slopeOffsetAxisPoint p m)]
  have hc : IsCompact (Kakeya.unitSegment T.base T.direction) :=
    isCompact_Icc.image (continuous_const.add (continuous_id.smul continuous_const))
  obtain ⟨a, ⟨t, ht, rfl⟩, hqa⟩ := exists_dist_le_of_mem_cthickening_closed hc.isClosed
    (planarTubeGridScale_pos (Nat.mul_pos hn hn)).le hq
  have ht' : |t - 1 / 2| ≤ 1 / 2 := abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have heq : T.base + t • T.direction =
      slopeOffsetAxisPoint p m + (t - 1 / 2) • slopeOffsetUnitDirection p := by
    change slopeOffsetAxisPoint p m - (1 / 2 : ℝ) • slopeOffsetUnitDirection p +
      t • slopeOffsetUnitDirection p = _
    module
  have haxis : ‖T.base + t • T.direction‖ ≤ 1 / 8 + 1 / 2 := by
    rw [heq]
    calc
      _ ≤ ‖slopeOffsetAxisPoint p m‖ + ‖(t - 1 / 2) • slopeOffsetUnitDirection p‖ := norm_add_le _ _
      _ ≤ _ := by
        simpa only [norm_smul, Real.norm_eq_abs, slopeOffsetUnitDirection_norm, mul_one] using
          add_le_add hmid ht'
  have hnorm : ‖q‖ ≤ 1 := by
    have h := norm_add_le (q - (T.base + t • T.direction)) (T.base + t • T.direction)
    rw [sub_add_cancel] at h
    rw [dist_eq_norm] at hqa
    linarith [planarTubeGridScale_le (Nat.mul_pos hn hn)]
  simpa only [Kakeya.DeltaTube.unitBall, Metric.mem_closedBall, dist_zero_right] using hnorm

theorem longitudinalTubeGridShading_window {n : ℕ} (hn : 0 < n) :
    IsInSlopeWindow (longitudinalTubeGridShading n) := by
  rintro p ⟨i, hi⟩
  have hp : ‖p‖ ≤ 1 := by
    simpa only [Kakeya.DeltaTube.unitBall, Metric.mem_closedBall, dist_zero_right] using
      longitudinalTubeGrid_in_unitBall hn i hi
  exact abs_le.mp ((PiLp.norm_apply_le p 2).trans hp)

theorem longitudinalTubeGrid_axis_projection_bound {n : ℕ} (hn : 0 < n)
    (i : Fin (longitudinalTubeGrid n).card) (q : Point3)
    (hq : q ∈ tubeAxisLine ((longitudinalTubeGrid n).tube i)) (hz : |q 2| ≤ 1) :
    |q 0 + q 2 * q 1| ≤ 3 * planarTubeGridMesh n := by
  let k := (Fintype.equivFin (LongitudinalTubeGridIndex n)).symm i
  let p := longitudinalTubeGridParams n k
  have hv : ((longitudinalTubeGrid n).tube i).direction 2 ≠ 0 := by
    have h := (longitudinalTubeGrid_lineClass hn i).vertical
    intro hz
    rw [hz, abs_zero] at h
    norm_num at h
  have hx := tubeAxisLine_coord_zero _ hv hq
  have hy := tubeAxisLine_coord_one _ hv hq
  rw [longitudinalTubeGrid_params] at hx hy
  rw [hx, hy]
  have ha := longitudinalTubeGrid_narrow_coord hn k.1.1
  have hu := longitudinalTubeGrid_narrow_coord hn k.2.1
  have hd := longitudinalTubeGrid_narrow_coord hn k.2.2
  let a := planarTubeGridMesh (n*n) * (k.1.1 : ℝ)
  let u := planarTubeGridMesh (n*n) * (k.2.1 : ℝ)
  let d := planarTubeGridMesh (n*n) * (k.2.2 : ℝ)
  have ha' : |a| ≤ planarTubeGridMesh n := by simpa [a, abs_of_nonneg ha.1] using ha.2
  have hu' : |u| ≤ planarTubeGridMesh n := by simpa [u, abs_of_nonneg hu.1] using hu.2
  have hd' : |d| ≤ planarTubeGridMesh n := by simpa [d, abs_of_nonneg hd.1] using hd.2
  have heq : p.a + p.c * q 2 + q 2 * (p.b + p.d * q 2) =
      (a + u * q 2) + d * (q 2) ^ 2 := by
    dsimp only [p, longitudinalTubeGridParams, a, u, d]
    ring
  change |p.a + p.c * q 2 + q 2 * (p.b + p.d * q 2)| ≤ _
  rw [heq]
  calc
    _ ≤ |a + u * q 2| + |d * (q 2)^2| := abs_add_le _ _
    _ ≤ (|a| + |u| * |q 2|) + |d| * |q 2|^2 := by
      have hfirst : |a + u * q 2| ≤ |a| + |u| * |q 2| := by
        have h := abs_add_le a (u*q 2)
        rw [abs_mul u (q 2)] at h
        exact h
      have hsecond : |d * (q 2)^2| = |d| * |q 2|^2 := by
        rw [abs_mul d ((q 2)^2), abs_pow (q 2) 2]
      rw [hsecond]
      linarith
    _ ≤ (planarTubeGridMesh n + planarTubeGridMesh n * 1) + planarTubeGridMesh n * 1^2 := by
      gcongr
      all_goals exact (planarTubeGridMesh_pos hn).le
    _ = _ := by ring

theorem longitudinalTubeGrid_projection_volume {n : ℕ} (hn : 0 < n) :
    volume (twistedUnion (longitudinalTubeGridShading n) (offsetObstructionSlope 0)) ≤
      ENNReal.ofReal (24 * planarTubeGridMesh n) := by
  have hdelta := planarTubeGridScale_pos (Nat.mul_pos hn hn)
  have hsubset : twistedUnion (longitudinalTubeGridShading n) (offsetObstructionSlope 0) ⊆
      offsetObstructionRectangle (6 * planarTubeGridMesh n) := by
    rintro _ ⟨p, ⟨i, hpi⟩, rfl⟩
    let T := (longitudinalTubeGrid n).tube i
    have hpnorm : ‖p‖ ≤ 1 := by
      simpa only [Kakeya.DeltaTube.unitBall, Metric.mem_closedBall, dist_zero_right] using
        longitudinalTubeGrid_in_unitBall hn i hpi
    have hc : IsCompact (Kakeya.unitSegment T.base T.direction) :=
      isCompact_Icc.image (continuous_const.add (continuous_id.smul continuous_const))
    obtain ⟨q, hq, hpq⟩ := exists_dist_le_of_mem_cthickening_closed hc.isClosed hdelta.le hpi
    have hqnorm : ‖q‖ ≤ 1 := by
      have hbody : q ∈ T.carrier := Metric.mem_cthickening_of_dist_le q q _ _ hq (by simpa using hdelta.le)
      simpa only [Kakeya.DeltaTube.unitBall, Metric.mem_closedBall, dist_zero_right] using
        longitudinalTubeGrid_in_unitBall hn i hbody
    have hqaxis : q ∈ tubeAxisLine T := by
      obtain ⟨t, ht, rfl⟩ := hq
      exact ⟨t, rfl⟩
    have haxis := longitudinalTubeGrid_axis_projection_bound hn i q hqaxis
      ((PiLp.norm_apply_le q 2).trans hqnorm)
    have hcoord (j : Fin 3) : |p j - q j| ≤ planarTubeGridScale (n*n) :=
      (abs_coord_sub_le_dist j).trans hpq
    have herr : |(p 0 + p 2 * p 1) - (q 0 + q 2 * q 1)| ≤
        3 * planarTubeGridScale (n*n) := by
      rw [show (p 0 + p 2*p 1) - (q 0 + q 2*q 1) =
        ((p 0-q 0) + p 2*(p 1-q 1)) + q 1*(p 2-q 2) by ring]
      calc
        _ ≤ |(p 0-q 0) + p 2*(p 1-q 1)| + |q 1*(p 2-q 2)| := abs_add_le _ _
        _ ≤ (|p 0-q 0| + |p 2| * |p 1-q 1|) + |q 1| * |p 2-q 2| := by
          simpa only [abs_mul] using
            _root_.add_le_add (abs_add_le (p 0-q 0) (p 2*(p 1-q 1))) (le_refl |q 1*(p 2-q 2)|)
        _ ≤ (planarTubeGridScale (n*n) + 1 * planarTubeGridScale (n*n)) +
            1 * planarTubeGridScale (n*n) := by
          exact _root_.add_le_add
            (_root_.add_le_add (hcoord 0)
              (mul_le_mul ((PiLp.norm_apply_le p 2).trans hpnorm) (hcoord 1)
                (abs_nonneg _) (by norm_num)))
            (mul_le_mul ((PiLp.norm_apply_le q 1).trans hqnorm) (hcoord 2)
              (abs_nonneg _) (by norm_num))
        _ = _ := by ring
    have hproj : |p 0 + p 2 * p 1| ≤ 6 * planarTubeGridMesh n := by
      have h := abs_add_le ((p 0+p 2*p 1)-(q 0+q 2*q 1)) (q 0+q 2*q 1)
      rw [sub_add_cancel] at h
      linarith [longitudinalTubeGrid_scale_le_width hn]
    have hz : |p 2| ≤ 1 := (PiLp.norm_apply_le p 2).trans hpnorm
    simpa [offsetObstructionRectangle, twistedProjection, EuclideanSpace.single_apply] using And.intro hproj hz
  calc
    _ ≤ volume (offsetObstructionRectangle (6 * planarTubeGridMesh n)) := measure_mono hsubset
    _ = ENNReal.ofReal (4 * (6 * planarTubeGridMesh n)) :=
      offsetObstructionRectangle_volume (by positivity [planarTubeGridMesh_pos hn])
    _ = _ := by congr 1; ring

end Kakeya.Assouad
end
