import MyLeanRepo.Kakeya.Assouad.PureWZ2.LongitudinalTubeGridGeometry

/-! Literal ordinary centered-dilation distinctness of the longitudinal grid. -/

noncomputable section
open MeasureTheory Set
namespace Kakeya.Assouad

theorem longitudinalTubeGrid_eq_of_centered_containment {n : ℕ} (hn : 0 < n)
    (i j : Fin (longitudinalTubeGrid n).card)
    (hij : ((longitudinalTubeGrid n).tube i).carrier ⊆
      wz2PaperCenteredDilatedCarrier 2 ((longitudinalTubeGrid n).tube j)) : i = j := by
  let p := tubeParamsOfTube ((longitudinalTubeGrid n).tube i)
  let q := tubeParamsOfTube ((longitudinalTubeGrid n).tube j)
  let delta := planarTubeGridScale (n*n)
  let mesh := planarTubeGridMesh (n*n)
  have hdelta : 0 < delta := planarTubeGridScale_pos (Nat.mul_pos hn hn)
  have hmesh : 0 < mesh := planarTubeGridMesh_pos (Nat.mul_pos hn hn)
  have hscale : delta = mesh / 64 := rfl
  have hb := longitudinalTubeGridParams_bounds hn
    ((Fintype.equivFin (LongitudinalTubeGridIndex n)).symm j)
  have hc : |q.c| ≤ 1 / 2 := by
    simpa only [q, longitudinalTubeGrid_params] using hb.2.2.1.trans (by norm_num)
  have hd : |q.d| ≤ 1 / 2 := by
    simpa only [q, longitudinalTubeGrid_params] using hb.2.2.2.trans (by norm_num)
  have hv : ((longitudinalTubeGrid n).tube j).direction 2 ≠ 0 := by
    have h := (longitudinalTubeGrid_lineClass hn j).vertical
    intro hz
    rw [hz, abs_zero] at h
    norm_num at h
  have hres (z : ℝ) (hz : |z| ≤ 1 / 8) :
      |p.a + p.c*z - (q.a+q.c*z)| ≤ 3*delta ∧
      |p.b + p.d*z - (q.b+q.d*z)| ≤ 3*delta := by
    have hpoint : slopeOffsetAxisPoint p z ∈ ((longitudinalTubeGrid n).tube i).carrier :=
      Metric.mem_cthickening_of_dist_le (slopeOffsetAxisPoint p z)
        (slopeOffsetAxisPoint p z) _ _ (longitudinalTubeGrid_axisPoint_mem_segment hn i z hz)
        (by simpa using hdelta.le)
    have haxis := wz2PaperCenteredDilatedCarrier_two_subset_axis hdelta.le
      ((longitudinalTubeGrid n).tube j) (hij hpoint)
    have h := vertical_line_neighbourhood_residual (by positivity : 0 ≤ 2*delta)
      ((longitudinalTubeGrid n).tube j) hv hc hd haxis
    norm_num at h
    simpa only [q, show (3 / 2 : ℝ) * (2*delta) = 3*delta by ring] using h
  have h0 := hres 0 (by norm_num)
  have h1 := hres (1 / 8) (by norm_num)
  simp only [mul_zero, add_zero] at h0
  have hA : |p.a-q.a| < mesh := by linarith [h0.1]
  have hC : |p.c-q.c| < mesh := by
    exact abs_lt.mpr ⟨by linarith [abs_le.mp h0.1, abs_le.mp h1.1],
      by linarith [abs_le.mp h0.1, abs_le.mp h1.1]⟩
  have hD : |p.d-q.d| < mesh := by
    exact abs_lt.mpr ⟨by linarith [abs_le.mp h0.2, abs_le.mp h1.2],
      by linarith [abs_le.mp h0.2, abs_le.mp h1.2]⟩
  have hU : |(p.b+p.c)-(q.b+q.c)| < mesh := by
    exact abs_lt.mpr ⟨by linarith [abs_le.mp h0.1, abs_le.mp h0.2, abs_le.mp h1.1],
      by linarith [abs_le.mp h0.1, abs_le.mp h0.2, abs_le.mp h1.1]⟩
  simp only [p, q, longitudinalTubeGrid_params, longitudinalTubeGridParams, sub_add_cancel] at hA hC hD hU
  have hAidx := fin_grid_eq_of_gap_lt hmesh _ _ hA
  have hCidx := fin_grid_eq_of_gap_lt hmesh _ _ hC
  have hDidx := fin_grid_eq_of_gap_lt hmesh _ _ hD
  have hUidx := fin_grid_eq_of_gap_lt hmesh _ _ hU
  apply (Fintype.equivFin (LongitudinalTubeGridIndex n)).symm.injective
  exact Prod.ext (Prod.ext hAidx hCidx) (Prod.ext hUidx hDidx)

theorem longitudinalTubeGrid_ordinary_distinct {n : ℕ} (hn : 0 < n) :
    WZ2PaperOrdinaryIsEssentiallyDistinct (longitudinalTubeGrid n) := by
  intro i j hij
  exact ⟨fun h => hij (longitudinalTubeGrid_eq_of_centered_containment hn i j h),
    fun h => hij (longitudinalTubeGrid_eq_of_centered_containment hn j i h).symm⟩

end Kakeya.Assouad
end
