import MyLeanRepo.Kakeya.Assouad.PureWZ2.SlopeOffsetRetubing
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Geometry of the unrestricted slope-offset obstruction

For f(z)=s+z, a family supported near the plane x+s*y=0 has twisted
projection width O(s*delta+1/s).  This file proves that estimate for the
actual ordinary tube carriers, without any nonconcentration assumption.
The separate grid construction verifies the counting hypotheses.
-/

noncomputable section
open MeasureTheory Set
namespace Kakeya.Assouad

def offsetObstructionSlope (s : ℝ) : SlopeFunction where
  toFun z := s + z
  contDiff := contDiff_const.add contDiff_id

@[simp] theorem offsetObstructionSlope_apply (s z : ℝ) :
    offsetObstructionSlope s z = s + z := rfl

theorem offsetObstructionSlope_nonsingular (s : ℝ) :
    (offsetObstructionSlope s).IsNonsingular := by
  have hd : deriv (offsetObstructionSlope s) = fun _ => (1 : ℝ) := by
    funext z
    change deriv (fun z : ℝ => s + z) z = 1
    simp
  intro z hz
  rw [hd]
  norm_num

def offsetObstructionRectangle (w : ℝ) : Set Point2 :=
  {p | |p 0| ≤ w ∧ |p 1| ≤ 1}

theorem offsetObstructionRectangle_volume {w : ℝ} (hw : 0 ≤ w) :
    volume (offsetObstructionRectangle w) = ENNReal.ofReal (4 * w) := by
  let e : Point2 ≃ᵐ (Fin 2 → ℝ) :=
    (EuclideanSpace.equiv (Fin 2) ℝ).toHomeomorph.toMeasurableEquiv
  let lower : Fin 2 → ℝ := ![-w, -1]
  let upper : Fin 2 → ℝ := ![w, 1]
  have hset : offsetObstructionRectangle w = e ⁻¹' Set.Icc lower upper := by
    ext p
    simp only [offsetObstructionRectangle, Set.mem_setOf_eq, Set.mem_preimage,
      Set.mem_Icc, abs_le]
    constructor
    · rintro ⟨⟨hxL, hxR⟩, ⟨hzL, hzR⟩⟩
      constructor <;> intro i <;> fin_cases i <;> simpa [e, lower, upper] using
        (by assumption)
    · rintro ⟨hl, hu⟩
      exact ⟨⟨hl 0, hu 0⟩, ⟨hl 1, hu 1⟩⟩
  rw [hset, (show MeasurePreserving e volume volume from
    PiLp.volume_preserving_ofLp (ι := Fin 2)).measure_preimage_equiv]
  rw [Real.volume_Icc_pi, Fin.prod_univ_two]
  simp only [lower, upper, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  rw [← ENNReal.ofReal_mul (by linarith : 0 ≤ w - -w)]
  congr 1
  ring

/-- Actual unit-segment tubes near a steep plane have small twisted images. -/
theorem offsetObstruction_projection_subset
    {delta : ℝ} (hdelta : 0 ≤ delta)
    {F : Kakeya.Streamlined.TubeFamily delta}
    (hbase : HasBoundedBase F 4)
    (Y : Kakeya.Streamlined.TubeShading F) (hwindow : IsInSlopeWindow Y)
    {s : ℝ} (hs : 1 ≤ s)
    (hplane : ∀ i q, q ∈ tubeAxisLine (F.tube i) → q 0 + s * q 1 = 0) :
    twistedUnion Y (offsetObstructionSlope s) ⊆
      offsetObstructionRectangle (3 * s * delta + 5 / s) := by
  rintro _ ⟨p, hp, rfl⟩
  obtain ⟨i, hpi⟩ := hp
  have hcompact : IsCompact (Kakeya.unitSegment (F.tube i).base (F.tube i).direction) :=
    isCompact_Icc.image (continuous_const.add (continuous_id.smul continuous_const))
  obtain ⟨q, hq, hpq⟩ := exists_dist_le_of_mem_cthickening_closed
    hcompact.isClosed hdelta (Y.subset_body i hpi)
  have hqaxis : q ∈ tubeAxisLine (F.tube i) := by
    obtain ⟨t, ht, rfl⟩ := hq
    exact ⟨t, rfl⟩
  have hqnorm : ‖q‖ ≤ 5 := by
    obtain ⟨t, ht, rfl⟩ := hq
    calc
      _ ≤ ‖(F.tube i).base‖ + ‖t • (F.tube i).direction‖ := norm_add_le _ _
      _ = ‖(F.tube i).base‖ + t := by
        rw [norm_smul, (F.tube i).direction_unit, Real.norm_eq_abs,
          abs_of_nonneg ht.1, mul_one]
      _ ≤ 5 := by linarith [hbase i, ht.2]
  have hspos : 0 < s := by linarith
  have hq1 : |q 1| ≤ 5 / s := by
    have hq0 : |q 0| ≤ 5 := (PiLp.norm_apply_le q 0).trans hqnorm
    have hplaneq := hplane i q hqaxis
    have heq : q 1 = -(q 0) / s := by apply (eq_div_iff hspos.ne').2; linarith
    rw [heq, abs_div, abs_neg, abs_of_pos hspos]
    exact div_le_div_of_nonneg_right hq0 hspos.le
  have hcoord (j : Fin 3) : |p j - q j| ≤ delta :=
    (abs_coord_sub_le_dist j).trans hpq
  have hy : |p 1| ≤ delta + 5 / s := by
    calc
      _ = |(p 1 - q 1) + q 1| := by ring_nf
      _ ≤ |p 1 - q 1| + |q 1| := abs_add_le _ _
      _ ≤ _ := add_le_add (hcoord 1) hq1
  have hz : |p 2| ≤ 1 := abs_le.mpr (hwindow ⟨i, hpi⟩)
  have hres : |p 0 + s * p 1| ≤ (1 + s) * delta := by
    have heq : p 0 + s * p 1 = (p 0 - q 0) + s * (p 1 - q 1) := by
      nlinarith [hplane i q hqaxis]
    rw [heq]
    calc
      _ ≤ |p 0 - q 0| + s * |p 1 - q 1| := by
        simpa only [abs_mul, abs_of_pos hspos] using abs_add_le (p 0 - q 0) (s * (p 1 - q 1))
      _ ≤ delta + s * delta := add_le_add (hcoord 0)
        (mul_le_mul_of_nonneg_left (hcoord 1) hspos.le)
      _ = _ := by ring
  have hproj : |p 0 + (s + p 2) * p 1| ≤ 3 * s * delta + 5 / s := by
    calc
      _ = |(p 0 + s * p 1) + p 2 * p 1| := by congr 1; ring
      _ ≤ |p 0 + s * p 1| + |p 2| * |p 1| := by
        simpa only [abs_mul] using abs_add_le (p 0 + s * p 1) (p 2 * p 1)
      _ ≤ (1 + s) * delta + 1 * (delta + 5 / s) := by gcongr
      _ ≤ _ := by nlinarith
  simpa [offsetObstructionRectangle, twistedProjection, EuclideanSpace.single_apply] using
    (show |p 0 + (s + p 2) * p 1| ≤ 3 * s * delta + 5 / s ∧ |p 2| ≤ 1 from ⟨hproj, hz⟩)

theorem offsetObstruction_projection_volume_le
    {delta : ℝ} (hdelta : 0 ≤ delta)
    {F : Kakeya.Streamlined.TubeFamily delta}
    (hbase : HasBoundedBase F 4)
    (Y : Kakeya.Streamlined.TubeShading F) (hwindow : IsInSlopeWindow Y)
    {s : ℝ} (hs : 1 ≤ s)
    (hplane : ∀ i q, q ∈ tubeAxisLine (F.tube i) → q 0 + s * q 1 = 0) :
    volume (twistedUnion Y (offsetObstructionSlope s)) ≤
      ENNReal.ofReal (12 * s * delta + 20 / s) := by
  apply (measure_mono (offsetObstruction_projection_subset hdelta hbase Y hwindow hs hplane)).trans
  rw [offsetObstructionRectangle_volume (by positivity)]
  apply ENNReal.ofReal_mono
  ring_nf
  exact le_rfl

end Kakeya.Assouad
end
