import MyLeanRepo.Kakeya.Assouad.PureWZ2.CenteredTubeWolff

/-!
# Longitudinal information retained by ordinary capsule containment

An ordinary unit-segment tube contained in a radius-r ordinary unit-segment
tube has midpoint within 2r of the containing midpoint. Consequently two
fine tubes in one ordinary coarse tube have center heights within 4r.
Supporting-line parameters alone do not record this coordinate.
-/

noncomputable section
open MeasureTheory Set
namespace Kakeya.Assouad

theorem ordinary_capsule_midpoint_dist_of_subset
    {delta r : ℝ} (hdelta : 0 ≤ delta) (hr : 0 ≤ r)
    (S : Kakeya.DeltaTube delta) (T : Kakeya.DeltaTube r)
    (hST : S.carrier ⊆ T.carrier) :
    dist (wz2PaperTubeMidpoint S) (wz2PaperTubeMidpoint T) ≤ 2 * r := by
  have hbase : S.base ∈ S.carrier := Metric.mem_cthickening_of_dist_le _ S.base _ _
    ⟨0, by norm_num, by simp⟩ (by simpa using hdelta)
  have hend : S.base + S.direction ∈ S.carrier := Metric.mem_cthickening_of_dist_le
    _ (S.base + S.direction) _ _ ⟨1, by norm_num, by simp⟩ (by simpa using hdelta)
  have hcompact : IsCompact (Kakeya.unitSegment T.base T.direction) :=
    isCompact_Icc.image (continuous_const.add (continuous_id.smul continuous_const))
  obtain ⟨a, ⟨u, hu, rfl⟩, ha⟩ :=
    exists_dist_le_of_mem_cthickening_closed hcompact.isClosed hr (hST hbase)
  obtain ⟨b, ⟨v, hv, rfl⟩, hb⟩ :=
    exists_dist_le_of_mem_cthickening_closed hcompact.isClosed hr (hST hend)
  have hlength : dist S.base (S.base + S.direction) = 1 := by
    rw [dist_eq_norm, show S.base - (S.base + S.direction) = -S.direction by module,
      norm_neg, S.direction_unit]
  have huv : dist (T.base + u • T.direction) (T.base + v • T.direction) = |u - v| := by
    rw [dist_eq_norm, show (T.base + u • T.direction) - (T.base + v • T.direction) =
      (u - v) • T.direction by module, norm_smul, Real.norm_eq_abs, T.direction_unit, mul_one]
  have hspan : 1 ≤ |u - v| + 2 * r := by
    have htriangle := dist_triangle S.base (T.base + u • T.direction) (S.base + S.direction)
    have htriangle' := dist_triangle (T.base + u • T.direction)
      (T.base + v • T.direction) (S.base + S.direction)
    rw [hlength] at htriangle
    rw [huv, dist_comm (T.base + v • T.direction) (S.base + S.direction)] at htriangle'
    linarith
  have hsum : |u + v - 1| ≤ 2 * r := by
    rcases le_total u v with huv' | hvu'
    · rw [abs_of_nonpos (sub_nonpos.mpr huv')] at hspan
      exact abs_le.mpr ⟨by linarith [hu.1, hv.1], by linarith [hu.2, hv.2]⟩
    · rw [abs_of_nonneg (sub_nonneg.mpr hvu')] at hspan
      exact abs_le.mpr ⟨by linarith [hu.1, hv.1], by linarith [hu.2, hv.2]⟩
  have heq : wz2PaperTubeMidpoint S - wz2PaperTubeMidpoint T =
      (1 / 2 : ℝ) • ((S.base - (T.base + u • T.direction)) +
        ((S.base + S.direction) - (T.base + v • T.direction))) +
      ((u + v - 1) / 2) • T.direction := by
    dsimp only [wz2PaperTubeMidpoint]
    module
  have hhalf : |(u + v - 1) / 2| ≤ r := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith
  rw [dist_eq_norm, heq]
  calc
    _ ≤ ‖(1 / 2 : ℝ) • ((S.base - (T.base + u • T.direction)) +
          ((S.base + S.direction) - (T.base + v • T.direction)))‖ +
        ‖((u + v - 1) / 2) • T.direction‖ := norm_add_le _ _
    _ ≤ (1 / 2 : ℝ) * (‖S.base - (T.base + u • T.direction)‖ +
          ‖(S.base + S.direction) - (T.base + v • T.direction)‖) + r := by
      simp only [norm_smul, Real.norm_eq_abs, T.direction_unit, mul_one,
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      exact add_le_add (mul_le_mul_of_nonneg_left (norm_add_le _ _) (by norm_num)) hhalf
    _ ≤ (1 / 2 : ℝ) * (r + r) + r := by
      rw [dist_eq_norm] at ha hb
      gcongr
    _ = _ := by ring

theorem ordinary_capsule_pair_center_height
    {delta r : ℝ} (hdelta : 0 ≤ delta) (hr : 0 ≤ r)
    (S U : Kakeya.DeltaTube delta) (T : Kakeya.DeltaTube r)
    (hST : S.carrier ⊆ T.carrier) (hUT : U.carrier ⊆ T.carrier) :
    |wz2PaperTubeMidpoint S 2 - wz2PaperTubeMidpoint U 2| ≤ 4 * r := by
  have hS := ordinary_capsule_midpoint_dist_of_subset hdelta hr S T hST
  have hU := ordinary_capsule_midpoint_dist_of_subset hdelta hr U T hUT
  calc
    _ ≤ dist (wz2PaperTubeMidpoint S) (wz2PaperTubeMidpoint U) := abs_coord_sub_le_dist _
    _ ≤ dist (wz2PaperTubeMidpoint S) (wz2PaperTubeMidpoint T) +
        dist (wz2PaperTubeMidpoint T) (wz2PaperTubeMidpoint U) := dist_triangle _ _ _
    _ ≤ 2 * r + 2 * r := by rw [dist_comm (wz2PaperTubeMidpoint T)]; gcongr
    _ = _ := by ring

end Kakeya.Assouad
end
