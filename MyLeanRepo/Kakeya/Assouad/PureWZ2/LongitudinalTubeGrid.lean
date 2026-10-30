import MyLeanRepo.Kakeya.Assouad.PureWZ2.PlanarTubeGridWolff
import MyLeanRepo.Kakeya.Assouad.PureWZ2.OrdinaryCapsuleParameterBounds

/-!
# A grid retaining the longitudinal position of each unit segment

The lines have parameters (a,u-c,c,d), where a,u,d vary in intervals of
width sqrt(delta). Their unit-segment center height varies on a coarser
grid. For the normalized slope f(z)=z, every axis projects to
a + u*z + d*z^2. The counting and projected-area estimates are separate.
-/

noncomputable section
open MeasureTheory Set
namespace Kakeya.Assouad

abbrev LongitudinalTubeGridIndex (n : ℕ) :=
  (Fin n × Fin (n * n)) × (Fin n × Fin n)

def longitudinalTubeGridParams (n : ℕ) (i : LongitudinalTubeGridIndex n) : TubeParams where
  a := planarTubeGridMesh (n*n) * (i.1.1 : ℝ)
  b := planarTubeGridMesh (n*n) * (i.2.1 : ℝ) - planarTubeGridMesh (n*n) * (i.1.2 : ℝ)
  c := planarTubeGridMesh (n*n) * (i.1.2 : ℝ)
  d := planarTubeGridMesh (n*n) * (i.2.2 : ℝ)

def longitudinalTubeGridCenter (n : ℕ) (i : LongitudinalTubeGridIndex n) : ℝ :=
  planarTubeGridMesh n * (i.1.1 : ℝ)

def longitudinalTubeGrid (n : ℕ) : Kakeya.Streamlined.TubeFamily (planarTubeGridScale (n*n)) where
  card := Fintype.card (LongitudinalTubeGridIndex n)
  tube i := slopeOffsetModelTube
    (longitudinalTubeGridParams n ((Fintype.equivFin (LongitudinalTubeGridIndex n)).symm i))
    (longitudinalTubeGridCenter n ((Fintype.equivFin (LongitudinalTubeGridIndex n)).symm i))
    (planarTubeGridScale (n*n))

theorem longitudinalTubeGrid_card (n : ℕ) : (longitudinalTubeGrid n).card = n ^ 5 := by
  simp only [longitudinalTubeGrid, LongitudinalTubeGridIndex, Fintype.card_prod, Fintype.card_fin]
  ring

theorem longitudinalTubeGrid_nonempty {n : ℕ} (hn : 0 < n) : (longitudinalTubeGrid n).Nonempty := by
  change 0 < (longitudinalTubeGrid n).card
  rw [longitudinalTubeGrid_card]
  positivity

theorem longitudinalTubeGrid_mesh_mul {n : ℕ} (hn : 0 < n) :
    planarTubeGridMesh (n*n) * (n : ℝ) = planarTubeGridMesh n := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  unfold planarTubeGridMesh
  simp only [Nat.cast_mul]
  field_simp

theorem longitudinalTubeGrid_scale_square {n : ℕ} (hn : 0 < n) :
    planarTubeGridMesh n ^ 2 = planarTubeGridScale (n*n) := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  unfold planarTubeGridScale planarTubeGridMesh
  simp only [Nat.cast_mul]
  field_simp

theorem longitudinalTubeGrid_scale_le_width {n : ℕ} (hn : 0 < n) :
    planarTubeGridScale (n*n) ≤ planarTubeGridMesh n := by
  rw [← longitudinalTubeGrid_scale_square hn]
  nlinarith [planarTubeGridMesh_pos hn, planarTubeGridMesh_le hn]

theorem longitudinalTubeGrid_narrow_coord {n : ℕ} (hn : 0 < n) (i : Fin n) :
    0 ≤ planarTubeGridMesh (n*n) * (i : ℝ) ∧
      planarTubeGridMesh (n*n) * (i : ℝ) ≤ planarTubeGridMesh n := by
  have hi : (i : ℝ) ≤ n := by exact_mod_cast i.isLt.le
  refine ⟨by positivity [planarTubeGridMesh_pos (Nat.mul_pos hn hn)], ?_⟩
  calc
    _ ≤ planarTubeGridMesh (n*n) * (n : ℝ) := by gcongr; exact (planarTubeGridMesh_pos (Nat.mul_pos hn hn)).le
    _ = _ := longitudinalTubeGrid_mesh_mul hn

theorem longitudinalTubeGrid_center_bounds {n : ℕ} (hn : 0 < n) (i : LongitudinalTubeGridIndex n) :
    |longitudinalTubeGridCenter n i| ≤ 1 / 64 := by
  have h := planarTubeGrid_coordinate_bounds hn i.1.1
  simpa only [longitudinalTubeGridCenter, abs_of_nonneg h.1] using h.2

theorem longitudinalTubeGridParams_bounds {n : ℕ} (hn : 0 < n) (i : LongitudinalTubeGridIndex n) :
    |(longitudinalTubeGridParams n i).a| ≤ 1 / 64 ∧
    |(longitudinalTubeGridParams n i).b| ≤ 1 / 64 ∧
    |(longitudinalTubeGridParams n i).c| ≤ 1 / 64 ∧
    |(longitudinalTubeGridParams n i).d| ≤ 1 / 64 := by
  have ha := longitudinalTubeGrid_narrow_coord hn i.1.1
  have hu := longitudinalTubeGrid_narrow_coord hn i.2.1
  have hd := longitudinalTubeGrid_narrow_coord hn i.2.2
  have hc := planarTubeGrid_coordinate_bounds (Nat.mul_pos hn hn) i.1.2
  have hw := planarTubeGridMesh_le hn
  dsimp only [longitudinalTubeGridParams]
  exact ⟨by rw [abs_of_nonneg ha.1]; exact ha.2.trans hw,
    abs_le.mpr ⟨by linarith, by linarith⟩,
    by rw [abs_of_nonneg hc.1]; exact hc.2,
    by rw [abs_of_nonneg hd.1]; exact hd.2.trans hw⟩

theorem longitudinalTubeGrid_params (n : ℕ) (i : Fin (longitudinalTubeGrid n).card) :
    tubeParamsOfTube ((longitudinalTubeGrid n).tube i) =
      longitudinalTubeGridParams n ((Fintype.equivFin (LongitudinalTubeGridIndex n)).symm i) :=
  slopeOffsetModelTube_params _ _ _

theorem longitudinalTubeGrid_center (n : ℕ) (i : Fin (longitudinalTubeGrid n).card) :
    wz2PaperTubeMidpoint ((longitudinalTubeGrid n).tube i) 2 =
      longitudinalTubeGridCenter n ((Fintype.equivFin (LongitudinalTubeGridIndex n)).symm i) := by
  simp [wz2PaperTubeMidpoint, longitudinalTubeGrid, slopeOffsetModelTube]

theorem longitudinalTubeGrid_lineClass {n : ℕ} (hn : 0 < n) :
    WZ1PaperIsLineClass (longitudinalTubeGrid n) := by
  intro i
  have h := longitudinalTubeGridParams_bounds hn ((Fintype.equivFin (LongitudinalTubeGridIndex n)).symm i)
  exact slopeOffsetModelTube_lineClass _ _ _ (h.1.trans (by norm_num))
    (h.2.1.trans (by norm_num)) (h.2.2.1.trans (by norm_num)) (h.2.2.2.trans (by norm_num))

theorem longitudinalTubeGrid_boundedBase {n : ℕ} (hn : 0 < n) :
    HasBoundedBase (longitudinalTubeGrid n) 4 := by
  intro i
  have h := longitudinalTubeGridParams_bounds hn ((Fintype.equivFin (LongitudinalTubeGridIndex n)).symm i)
  have hm := longitudinalTubeGrid_center_bounds hn ((Fintype.equivFin (LongitudinalTubeGridIndex n)).symm i)
  exact slopeOffsetModelTube_base_bound _ _ _ (h.1.trans (by norm_num))
    (h.2.1.trans (by norm_num)) (h.2.2.1.trans (by norm_num))
    (h.2.2.2.trans (by norm_num)) (hm.trans (by norm_num))

theorem longitudinalTubeGrid_axisPoint_mem_segment {n : ℕ} (hn : 0 < n)
    (i : Fin (longitudinalTubeGrid n).card) (z : ℝ) (hz : |z| ≤ 1 / 8) :
    slopeOffsetAxisPoint (tubeParamsOfTube ((longitudinalTubeGrid n).tube i)) z ∈
      Kakeya.unitSegment ((longitudinalTubeGrid n).tube i).base ((longitudinalTubeGrid n).tube i).direction := by
  let k := (Fintype.equivFin (LongitudinalTubeGridIndex n)).symm i
  let p := longitudinalTubeGridParams n k
  let m := longitudinalTubeGridCenter n k
  have hp := longitudinalTubeGridParams_bounds hn k
  have hm := longitudinalTubeGrid_center_bounds hn k
  have hzm : |z - m| ≤ 1 / 4 := by
    have hm' : |m| ≤ 1 / 64 := hm
    exact abs_le.mpr ⟨by linarith [abs_le.mp hz, abs_le.mp hm'],
      by linarith [abs_le.mp hz, abs_le.mp hm']⟩
  have hnorm := slopeOffsetAxisVector_norm_le_two p (hp.2.2.1.trans (by norm_num))
    (hp.2.2.2.trans (by norm_num))
  have ht : |‖slopeOffsetAxisVector p‖ * (z - m)| ≤ 1 / 2 := by
    rw [abs_mul, abs_of_nonneg (norm_nonneg _)]
    calc
      _ ≤ 2 * (1 / 4 : ℝ) := by gcongr
      _ = _ := by norm_num
  rw [longitudinalTubeGrid_params]
  refine ⟨‖slopeOffsetAxisVector p‖ * (z - m) + 1 / 2,
    ⟨by linarith [abs_le.mp ht], by linarith [abs_le.mp ht]⟩, ?_⟩
  exact slopeOffsetModelTube_axisPoint_formula p m (planarTubeGridScale (n*n)) z

def longitudinalTubeGridShading (n : ℕ) : Kakeya.Streamlined.TubeShading (longitudinalTubeGrid n) where
  carrier i := ((longitudinalTubeGrid n).tube i).carrier
  measurable_carrier _ := Metric.isClosed_cthickening.measurableSet
  subset_body _ := Set.Subset.rfl

theorem longitudinalTubeGridShading_dense (n : ℕ) : (longitudinalTubeGridShading n).IsLambdaDense 1 := by
  change 1 * (∑ i, volume (((longitudinalTubeGrid n).tube i).carrier)) ≤
    ∑ i, volume (((longitudinalTubeGrid n).tube i).carrier)
  simp

end Kakeya.Assouad
end
