import MyLeanRepo.Kakeya.Assouad.PureWZ2.SlopeOffsetGeometry
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperCarrierContainmentLineDistance

/-!
# Retubing an actual paper terminal after centering its slope

The supporting lines are transformed by `slopeOffsetLinear`.  Unit segments
are centered at a common height.  On a slab of width 1/4, the transformed
paper shading lies in the corresponding ordinary radius-12δ tubes.
-/

noncomputable section
open MeasureTheory Set
namespace Kakeya.Assouad

def slopeOffsetAxisPoint (p : TubeParams) (z : ℝ) : Point3 :=
  point3 (p.a + p.c * z) (p.b + p.d * z) z

def slopeOffsetAxisVector (p : TubeParams) : Point3 := point3 p.c p.d 1

@[simp] theorem slopeOffsetAxisPoint_coord_zero (p : TubeParams) (z : ℝ) :
    slopeOffsetAxisPoint p z 0 = p.a + p.c * z := by
  simp only [slopeOffsetAxisPoint, point3_coord0]

@[simp] theorem slopeOffsetAxisPoint_coord_one (p : TubeParams) (z : ℝ) :
    slopeOffsetAxisPoint p z 1 = p.b + p.d * z := by
  simp only [slopeOffsetAxisPoint, point3_coord1]

@[simp] theorem slopeOffsetAxisPoint_coord_two (p : TubeParams) (z : ℝ) :
    slopeOffsetAxisPoint p z 2 = z := by
  simp only [slopeOffsetAxisPoint, point3_coord2]

@[simp] theorem slopeOffsetAxisVector_coord_zero (p : TubeParams) :
    slopeOffsetAxisVector p 0 = p.c := by simp only [slopeOffsetAxisVector, point3_coord0]

@[simp] theorem slopeOffsetAxisVector_coord_one (p : TubeParams) :
    slopeOffsetAxisVector p 1 = p.d := by simp only [slopeOffsetAxisVector, point3_coord1]

@[simp] theorem slopeOffsetAxisVector_coord_two (p : TubeParams) :
    slopeOffsetAxisVector p 2 = 1 := by simp only [slopeOffsetAxisVector, point3_coord2]

theorem slopeOffsetAxisVector_norm_pos (p : TubeParams) :
    0 < ‖slopeOffsetAxisVector p‖ := by
  apply norm_pos_iff.mpr
  intro h
  have := congrArg (fun v : Point3 => v 2) h
  simpa only [slopeOffsetAxisVector_coord_two, PiLp.zero_apply, one_ne_zero] using this

def slopeOffsetUnitDirection (p : TubeParams) : Point3 :=
  ‖slopeOffsetAxisVector p‖⁻¹ • slopeOffsetAxisVector p

theorem slopeOffsetUnitDirection_norm (p : TubeParams) :
    ‖slopeOffsetUnitDirection p‖ = 1 := by
  simp only [slopeOffsetUnitDirection, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
  exact inv_mul_cancel₀ (slopeOffsetAxisVector_norm_pos p).ne'

/-- The line's unit segment is centered at height `m`. -/
def slopeOffsetModelTube (p : TubeParams) (m r : ℝ) : Kakeya.DeltaTube r where
  base := slopeOffsetAxisPoint p m - (1 / 2 : ℝ) • slopeOffsetUnitDirection p
  direction := slopeOffsetUnitDirection p
  direction_unit := slopeOffsetUnitDirection_norm p

theorem slopeOffsetModelTube_axisPoint_formula (p : TubeParams) (m r z : ℝ) :
    (slopeOffsetModelTube p m r).base +
        (‖slopeOffsetAxisVector p‖ * (z - m) + 1 / 2) •
          (slopeOffsetModelTube p m r).direction = slopeOffsetAxisPoint p z := by
  ext i
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hi with rfl | rfl | rfl <;>
    norm_num [slopeOffsetModelTube, slopeOffsetUnitDirection] <;>
    field_simp [(slopeOffsetAxisVector_norm_pos p).ne'] <;> ring

theorem slopeOffsetModelTube_params (p : TubeParams) (m r : ℝ) :
    tubeParamsOfTube (slopeOffsetModelTube p m r) = p := by
  apply TubeParams.ext <;>
    simp [tubeParamsOfTube, slopeOffsetModelTube, slopeOffsetUnitDirection] <;>
    field_simp [(slopeOffsetAxisVector_norm_pos p).ne'] <;> ring

theorem slopeOffsetModelTube_axisPoint_mem (p : TubeParams) (m r z : ℝ) :
    slopeOffsetAxisPoint p z ∈ tubeAxisLine (slopeOffsetModelTube p m r) := by
  exact ⟨‖slopeOffsetAxisVector p‖ * (z - m) + 1 / 2,
    (slopeOffsetModelTube_axisPoint_formula p m r z).symm⟩

theorem slopeOffsetAxisVector_norm_le_two (p : TubeParams)
    (hc : |p.c| ≤ 1 / 2) (hd : |p.d| ≤ 1 / 2) :
    ‖slopeOffsetAxisVector p‖ ≤ 2 := by
  have hnorm := point3_coord_norm_sq (slopeOffsetAxisVector p)
  simp only [slopeOffsetAxisVector_coord_zero, slopeOffsetAxisVector_coord_one,
    slopeOffsetAxisVector_coord_two] at hnorm
  nlinarith [sq_abs p.c, sq_abs p.d, abs_le.mp hc, abs_le.mp hd,
    norm_nonneg (slopeOffsetAxisVector p)]

theorem slopeOffsetModelTube_vertical (p : TubeParams) (m r : ℝ)
    (hc : |p.c| ≤ 1 / 2) (hd : |p.d| ≤ 1 / 2) :
    (1 / 2 : ℝ) ≤ (slopeOffsetModelTube p m r).direction 2 := by
  have hn := slopeOffsetAxisVector_norm_pos p
  have hn2 := slopeOffsetAxisVector_norm_le_two p hc hd
  change (1 / 2 : ℝ) ≤ (‖slopeOffsetAxisVector p‖⁻¹ • slopeOffsetAxisVector p) 2
  simp only [PiLp.smul_apply, smul_eq_mul, slopeOffsetAxisVector, point3_coord2, mul_one]
  rw [← one_div]
  exact (le_div_iff₀ hn).2 (by linarith)

theorem slopeOffsetModelTube_lineClass (p : TubeParams) (m r : ℝ)
    (ha : |p.a| ≤ 1 / 3) (hb : |p.b| ≤ 1 / 3)
    (hc : |p.c| ≤ 1 / 2) (hd : |p.d| ≤ 1 / 2) :
    WZ1PaperTubeInLineClass (slopeOffsetModelTube p m r) := by
  have hv := slopeOffsetModelTube_vertical p m r hc hd
  have hz : wz1TubeAxisZeroPoint (slopeOffsetModelTube p m r) =
      slopeOffsetAxisPoint p 0 := by
    ext i
    have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases hi with rfl | rfl | rfl <;>
      norm_num [wz1TubeAxisZeroPoint, slopeOffsetModelTube,
        slopeOffsetUnitDirection] <;>
      field_simp [(slopeOffsetAxisVector_norm_pos p).ne'] <;> ring
  refine ⟨?_, ?_, ?_⟩
  · simpa only [wz1PaperDirection, if_pos (by linarith :
      0 ≤ (slopeOffsetModelTube p m r).direction 2)] using hv
  · simpa only [hz, slopeOffsetAxisPoint, mul_zero, add_zero, point3_coord0] using ha
  · simpa only [hz, slopeOffsetAxisPoint, mul_zero, add_zero, point3_coord1] using hb

theorem slopeOffsetModelTube_base_bound (p : TubeParams) (m r : ℝ)
    (ha : |p.a| ≤ 1 / 12) (hb : |p.b| ≤ 1 / 12)
    (hc : |p.c| ≤ 1 / 2) (hd : |p.d| ≤ 1 / 2) (hm : |m| ≤ 1) :
    ‖(slopeOffsetModelTube p m r).base‖ ≤ 4 := by
  have hcoord (x y : ℝ) (hx : |x| ≤ 1 / 12) (hy : |y| ≤ 1 / 2) :
      |x + y * m| ≤ 1 := by
    calc
      _ ≤ |x| + |y| * |m| := by simpa only [abs_mul] using abs_add_le x (y * m)
      _ ≤ (1 / 12 : ℝ) + (1 / 2) * 1 := by gcongr
      _ ≤ 1 := by norm_num
  have hx := hcoord p.a p.c ha hc
  have hy := hcoord p.b p.d hb hd
  have hn := point3_coord_norm_sq (slopeOffsetAxisPoint p m)
  simp only [slopeOffsetAxisPoint_coord_zero, slopeOffsetAxisPoint_coord_one,
    slopeOffsetAxisPoint_coord_two] at hn
  have hpoint : ‖slopeOffsetAxisPoint p m‖ ≤ 2 := by
    nlinarith [abs_le.mp hx, abs_le.mp hy, abs_le.mp hm,
      sq_abs (p.a + p.c * m), sq_abs (p.b + p.d * m), sq_abs m,
      norm_nonneg (slopeOffsetAxisPoint p m)]
  calc
    _ ≤ ‖slopeOffsetAxisPoint p m‖ + ‖(1 / 2 : ℝ) • slopeOffsetUnitDirection p‖ :=
      norm_sub_le _ _
    _ ≤ 2 + (1 / 2 : ℝ) := by
      simpa [norm_smul, slopeOffsetUnitDirection_norm] using hpoint
    _ ≤ 4 := by norm_num

theorem slopeOffsetModelTube_slab_axisPoint_mem_segment
    (p : TubeParams) (m r z : ℝ)
    (hc : |p.c| ≤ 1 / 2) (hd : |p.d| ≤ 1 / 2)
    (hz : |z - m| ≤ 1 / 8) :
    slopeOffsetAxisPoint p z ∈ Kakeya.unitSegment
      (slopeOffsetModelTube p m r).base (slopeOffsetModelTube p m r).direction := by
  have hn := slopeOffsetAxisVector_norm_pos p
  have hn2 := slopeOffsetAxisVector_norm_le_two p hc hd
  have ht : |‖slopeOffsetAxisVector p‖ * (z - m)| ≤ 1 / 4 := by
    rw [abs_mul, abs_of_pos hn]
    calc
      _ ≤ (2 : ℝ) * (1 / 8) := by gcongr
      _ = _ := by norm_num
  refine ⟨‖slopeOffsetAxisVector p‖ * (z - m) + 1 / 2, ?_,
    slopeOffsetModelTube_axisPoint_formula p m r z⟩
  exact ⟨by linarith [abs_le.mp ht], by linarith [abs_le.mp ht]⟩

theorem slopeOffsetParams_bounds_of_lineClass
    {delta : ℝ} (T : Kakeya.DeltaTube delta) (hT : WZ1PaperTubeInLineClass T)
    (s : ℝ) :
    |(slopeOffsetParams s (tubeParamsOfTube T)).a| ≤ 1 / 12 ∧
    |(slopeOffsetParams s (tubeParamsOfTube T)).b| ≤ 1 / 12 ∧
    |(slopeOffsetParams s (tubeParamsOfTube T)).c| ≤ 1 / 2 ∧
    |(slopeOffsetParams s (tubeParamsOfTube T)).d| ≤ 1 / 2 := by
  have hab : |(tubeParamsOfTube T).a| ≤ 1 / 3 ∧
      |(tubeParamsOfTube T).b| ≤ 1 / 3 := by
    convert hT.2 using 1 <;>
      simp [tubeParamsOfTube, wz1TubeAxisZeroPoint, div_eq_mul_inv,
        mul_assoc, mul_comm, mul_left_comm]
  have hv : 0 < |T.direction 2| := by linarith [hT.vertical]
  have hcoord (i : Fin 3) : |T.direction i| ≤ 1 := by
    simpa only [T.direction_unit, Real.norm_eq_abs] using PiLp.norm_apply_le T.direction i
  have hratio (i : Fin 3) : |T.direction i / T.direction 2| ≤ 2 := by
    rw [abs_div]
    apply (div_le_iff₀ hv).2
    linarith [hcoord i, hT.vertical]
  exact slopeOffsetParams_bounds s (tubeParamsOfTube T) hab.1 hab.2 (hratio 0) (hratio 1)

/-- Exact action on every point of the supplied supporting line. -/
theorem slopeOffsetLinear_axis_point
    {delta : ℝ} (T : Kakeya.DeltaTube delta) (hT : WZ1PaperTubeInLineClass T)
    (s : ℝ) {q : Point3} (hq : q ∈ tubeAxisLine T) :
    slopeOffsetLinear s q =
      slopeOffsetAxisPoint (slopeOffsetParams s (tubeParamsOfTube T)) (q 2) := by
  have hv : T.direction 2 ≠ 0 := by
    intro h
    have := hT.vertical
    simp only [h, abs_zero] at this
    linarith
  have hx := tubeAxisLine_coord_zero T hv hq
  have hy := tubeAxisLine_coord_one T hv hq
  ext i
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hi with rfl | rfl | rfl <;>
    simp [slopeOffsetParams, hx, hy] <;> ring

theorem slopeOffsetLinear_axis_image
    {delta : ℝ} (T : Kakeya.DeltaTube delta) (hT : WZ1PaperTubeInLineClass T)
    (s m r : ℝ) :
    slopeOffsetLinear s '' tubeAxisLine T =
      tubeAxisLine (slopeOffsetModelTube (slopeOffsetParams s (tubeParamsOfTube T)) m r) := by
  let p := slopeOffsetParams s (tubeParamsOfTube T)
  have hb := slopeOffsetParams_bounds_of_lineClass T hT s
  have hvT : T.direction 2 ≠ 0 := by
    intro h
    have := hT.vertical
    simp only [h, abs_zero] at this
    linarith
  have hv : (slopeOffsetModelTube p m r).direction 2 ≠ 0 := by
    have := slopeOffsetModelTube_vertical p m r hb.2.2.1 hb.2.2.2
    linarith
  apply Set.Subset.antisymm
  · rintro _ ⟨q, hq, rfl⟩
    rw [slopeOffsetLinear_axis_point T hT s hq]
    exact slopeOffsetModelTube_axisPoint_mem p m r (q 2)
  · intro q hq
    refine ⟨tubeAxisPointAtHeight T (q 2), tubeAxisPointAtHeight_mem T (q 2), ?_⟩
    rw [slopeOffsetLinear_axis_point T hT s (tubeAxisPointAtHeight_mem T (q 2)),
      tubeAxisPointAtHeight_coord_two T hvT (q 2)]
    have hx := tubeAxisLine_coord_zero (slopeOffsetModelTube p m r) hv hq
    have hy := tubeAxisLine_coord_one (slopeOffsetModelTube p m r) hv hq
    rw [slopeOffsetModelTube_params] at hx hy
    ext i
    have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases hi with rfl | rfl | rfl <;> simp [← hx, ← hy, p]

theorem slopeOffsetLinear_cube_subset (s : ℝ) :
    slopeOffsetLinear s '' Kakeya.Streamlined.axisBox 2 2 2 ⊆
      Kakeya.Streamlined.axisBox 2 2 2 := by
  rintro _ ⟨p, hp, rfl⟩
  have hp' : |p 0| ≤ 1 ∧ |p 1| ≤ 1 ∧ |p 2| ≤ 1 := by
    simpa [Kakeya.Streamlined.axisBox] using hp
  have hp0 := hp'.1
  have hp1 := hp'.2.1
  have hk := (slopeOffsetScale_pos s).le
  have hks : slopeOffsetScale s * |s| ≤ 1 / 4 := by
    nlinarith [slopeOffsetScale_mul_one_add_abs s, slopeOffsetScale_pos s]
  have hx : |slopeOffsetLinear s p 0| ≤ 1 := by
    rw [slopeOffsetLinear_coord_zero, abs_mul, abs_of_pos (slopeOffsetScale_pos s)]
    calc
      _ ≤ slopeOffsetScale s * (|p 0| + |s| * |p 1|) := by
        gcongr
        simpa only [abs_mul] using abs_add_le (p 0) (s * p 1)
      _ ≤ slopeOffsetScale s * (1 + |s| * 1) := by gcongr
      _ = 1 / 4 := by simpa using slopeOffsetScale_mul_one_add_abs s
      _ ≤ 1 := by norm_num
  have hy : |slopeOffsetLinear s p 1| ≤ 1 := by
    rw [slopeOffsetLinear_coord_one, abs_mul, abs_of_pos (slopeOffsetScale_pos s)]
    calc
      _ ≤ (1 / 4 : ℝ) * 1 := by gcongr; exact slopeOffsetScale_le_quarter s
      _ ≤ 1 := by norm_num
  simpa [Kakeya.Streamlined.axisBox] using
    (show |slopeOffsetLinear s p 0| ≤ 1 ∧
      |slopeOffsetLinear s p 1| ≤ 1 ∧ |slopeOffsetLinear s p 2| ≤ 1 from
        ⟨hx, hy, by simpa using hp'.2.2⟩)

/-- The complete source paper body maps inside the retubed paper body.
This is the carrier containment used for CWA, independently of the slab. -/
theorem slopeOffsetLinear_paperCarrier_subset
    {delta : ℝ} (hdelta : 0 ≤ delta)
    (T : Kakeya.DeltaTube delta) (hT : WZ1PaperTubeInLineClass T) (s m : ℝ) :
    slopeOffsetLinear s '' wz1PaperTubeCarrier T ⊆
      wz1PaperTubeCarrier
        (slopeOffsetModelTube (slopeOffsetParams s (tubeParamsOfTube T)) m (12 * delta)) := by
  rintro _ ⟨p, hp, rfl⟩
  obtain ⟨q, hq, hpq⟩ := exists_dist_le_of_mem_cthickening_closed
    (isClosed_tubeAxisLine T) (by positivity : 0 ≤ 6 * delta) hp.1
  refine ⟨?_, slopeOffsetLinear_cube_subset s ⟨p, hp.2, rfl⟩⟩
  apply Metric.mem_cthickening_of_dist_le _ (slopeOffsetLinear s q)
  · rw [← slopeOffsetLinear_axis_image T hT]
    exact ⟨q, hq, rfl⟩
  · exact (slopeOffsetLinear_dist_le s p q).trans (by linarith)

/-- The slab's actual image lies in the ordinary unit-segment carrier. -/
theorem slopeOffsetLinear_slabCarrier_subset
    {delta : ℝ} (hdelta : 0 ≤ delta)
    (T : Kakeya.DeltaTube delta) (hT : WZ1PaperTubeInLineClass T) (s m : ℝ) :
    slopeOffsetLinear s ''
        (wz1PaperTubeCarrier T ∩ horizontalSlab (m - 1 / 8) (m + 1 / 8)) ⊆
      (slopeOffsetModelTube (slopeOffsetParams s (tubeParamsOfTube T)) m (12 * delta)).carrier := by
  rintro _ ⟨p, hp, rfl⟩
  obtain ⟨q, hq, hpq⟩ := exists_dist_le_of_mem_cthickening_closed
    (isClosed_tubeAxisLine T) (by positivity : 0 ≤ 6 * delta) hp.1.1
  let q₀ := wz1PaperAxisPointAtHeight T (p 2)
  have hq₀ := wz1PaperAxisPointAtHeight_mem_axis T (p 2)
  have hdist : dist p q₀ ≤ 12 * delta := by
    have h := wz1Paper_axisPointAtHeight_dist_point_le_two_mul hT p q hq
    dsimp only [q₀]
    rw [dist_comm]
    linarith
  have hb := slopeOffsetParams_bounds_of_lineClass T hT s
  have himage : slopeOffsetLinear s q₀ =
      slopeOffsetAxisPoint (slopeOffsetParams s (tubeParamsOfTube T)) (p 2) := by
    rw [slopeOffsetLinear_axis_point T hT s hq₀]
    rw [wz1PaperAxisPointAtHeight_coord_two hT]
  apply Metric.mem_cthickening_of_dist_le _ (slopeOffsetLinear s q₀)
  · rw [himage]
    apply slopeOffsetModelTube_slab_axisPoint_mem_segment _ m _ _ hb.2.2.1 hb.2.2.2
    exact abs_le.mpr ⟨by linarith [hp.2.1], by linarith [hp.2.2]⟩
  · exact (slopeOffsetLinear_dist_le s p q₀).trans hdist

end Kakeya.Assouad
end
