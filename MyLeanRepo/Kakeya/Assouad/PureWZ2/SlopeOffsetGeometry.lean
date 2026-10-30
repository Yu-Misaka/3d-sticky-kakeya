import MyLeanRepo.Kakeya.Assouad.ProjectionNormalization
import MyLeanRepo.Kakeya.Assouad.AnisotropicRescaling.TubeParameters
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12NestedJohnCWATransport
import Mathlib.Analysis.Normed.Lp.Matrix
import MyLeanRepo.Kakeya.Assouad.WZ1.AnchoredRescalingGeometry

/-!
# A bounded coordinate change that centers the actual slope

For s=f(0), send (x,y,z) to (k(x+s y),k y,z), k=1/(4(1+|s|)).
The target slope is f-s.  This acts on the supplied points and supporting
lines, and scales their twisted image horizontally by exactly k.
The spatial Jacobian is k², so the CWA/density cost is explicit.
-/

noncomputable section
open MeasureTheory Set
namespace Kakeya.Assouad

def slopeOffsetScale (s : ℝ) : ℝ := (4 * (1 + |s|))⁻¹

theorem slopeOffsetScale_pos (s : ℝ) : 0 < slopeOffsetScale s := by
  unfold slopeOffsetScale
  positivity

theorem slopeOffsetScale_le_quarter (s : ℝ) : slopeOffsetScale s ≤ 1 / 4 := by
  unfold slopeOffsetScale
  rw [← one_div (4 * (1 + |s|))]
  apply (div_le_iff₀ (by positivity)).2
  nlinarith [abs_nonneg s]

theorem slopeOffsetScale_mul_one_add_abs (s : ℝ) :
    slopeOffsetScale s * (1 + |s|) = 1 / 4 := by
  unfold slopeOffsetScale
  field_simp

/-- The spatial normalization, with its exact inverse. -/
def slopeOffsetLinear (s : ℝ) : Point3 ≃ₗ[ℝ] Point3 where
  toFun p := point3 (slopeOffsetScale s * (p 0 + s * p 1))
    (slopeOffsetScale s * p 1) (p 2)
  invFun p := point3 ((slopeOffsetScale s)⁻¹ * (p 0 - s * p 1))
    ((slopeOffsetScale s)⁻¹ * p 1) (p 2)
  left_inv p := by
    ext i
    fin_cases i <;> simp [point3] <;>
      field_simp [(slopeOffsetScale_pos s).ne'] <;> ring
  right_inv p := by
    ext i
    fin_cases i <;> simp [point3] <;>
      field_simp [(slopeOffsetScale_pos s).ne'] <;> ring
  map_add' p q := by
    ext i
    fin_cases i <;> simp [point3] <;> ring
  map_smul' a p := by
    ext i
    fin_cases i <;> simp [point3] <;> ring

@[simp] theorem slopeOffsetLinear_coord_zero (s : ℝ) (p : Point3) :
    slopeOffsetLinear s p 0 = slopeOffsetScale s * (p 0 + s * p 1) := by
  simp [slopeOffsetLinear, point3]

@[simp] theorem slopeOffsetLinear_coord_one (s : ℝ) (p : Point3) :
    slopeOffsetLinear s p 1 = slopeOffsetScale s * p 1 := by simp [slopeOffsetLinear, point3]

@[simp] theorem slopeOffsetLinear_coord_two (s : ℝ) (p : Point3) :
    slopeOffsetLinear s p 2 = p 2 := by simp [slopeOffsetLinear, point3]

theorem slopeOffsetLinear_det (s : ℝ) :
    LinearMap.det (slopeOffsetLinear s : Point3 →ₗ[ℝ] Point3) = slopeOffsetScale s ^ 2 := by
  let mat : Matrix (Fin 3) (Fin 3) ℝ :=
    !![slopeOffsetScale s, slopeOffsetScale s * s, 0;
       0, slopeOffsetScale s, 0; 0, 0, 1]
  have heq : (slopeOffsetLinear s : Point3 →ₗ[ℝ] Point3) = Matrix.toLpLin 2 2 mat := by
    ext p i
    have hmatrix := Matrix.ofLp_toLpLin (p := (2 : ENNReal)) (q := (2 : ENNReal)) mat p
    have hi := congr_fun hmatrix i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, mat,
      slopeOffsetLinear, point3] at hi ⊢ <;> linarith
  rw [heq, LinearMap.det_toLpLin]
  simp [mat, Matrix.det_fin_three]
  ring

theorem slopeOffsetLinear_volume_image (s : ℝ) (E : Set Point3) :
    volume (slopeOffsetLinear s '' E) =
      ENNReal.ofReal (slopeOffsetScale s ^ 2) * volume E := by
  change volume ((slopeOffsetLinear s : Point3 →ₗ[ℝ] Point3) '' E) = _
  rw [MeasureTheory.Measure.addHaar_image_linearMap, slopeOffsetLinear_det,
    abs_of_nonneg (sq_nonneg _)]

theorem slopeOffsetLinear_volume_inverse (s : ℝ) (E : Set Point3) :
    volume ((slopeOffsetLinear s).symm '' E) =
      ENNReal.ofReal ((slopeOffsetScale s ^ 2)⁻¹) * volume E := by
  change volume (((slopeOffsetLinear s).symm : Point3 →ₗ[ℝ] Point3) '' E) = _
  rw [MeasureTheory.Measure.addHaar_image_linearMap, LinearEquiv.det_coe_symm,
    slopeOffsetLinear_det, abs_of_nonneg (by positivity)]

/-- The exact parameter action on a supporting line. -/
def slopeOffsetParams (s : ℝ) (p : TubeParams) : TubeParams where
  a := slopeOffsetScale s * (p.a + s * p.b)
  b := slopeOffsetScale s * p.b
  c := slopeOffsetScale s * (p.c + s * p.d)
  d := slopeOffsetScale s * p.d

private theorem slopeOffset_combination_bound
    (s B x y : ℝ) (hB : 0 ≤ B) (hx : |x| ≤ B) (hy : |y| ≤ B) :
    |slopeOffsetScale s * (x + s * y)| ≤ B / 4 := by
  have hk : 0 ≤ slopeOffsetScale s := (slopeOffsetScale_pos s).le
  rw [abs_mul, abs_of_pos (slopeOffsetScale_pos s)]
  calc
    _ ≤ slopeOffsetScale s * (|x| + |s| * |y|) := by
      gcongr
      simpa only [abs_mul] using abs_add_le x (s * y)
    _ ≤ slopeOffsetScale s * (B + |s| * B) := by gcongr
    _ = (slopeOffsetScale s * (1 + |s|)) * B := by ring
    _ = B / 4 := by rw [slopeOffsetScale_mul_one_add_abs]; ring

theorem slopeOffsetParams_bounds
    (s : ℝ) (p : TubeParams)
    (ha : |p.a| ≤ 1 / 3) (hb : |p.b| ≤ 1 / 3)
    (hc : |p.c| ≤ 2) (hd : |p.d| ≤ 2) :
    |(slopeOffsetParams s p).a| ≤ 1 / 12 ∧
    |(slopeOffsetParams s p).b| ≤ 1 / 12 ∧
    |(slopeOffsetParams s p).c| ≤ 1 / 2 ∧
    |(slopeOffsetParams s p).d| ≤ 1 / 2 := by
  have ha' := slopeOffset_combination_bound s (1 / 3) p.a p.b (by norm_num) ha hb
  have hc' := slopeOffset_combination_bound s 2 p.c p.d (by norm_num) hc hd
  have hb' : |slopeOffsetScale s * p.b| ≤ 1 / 12 := by
    rw [abs_mul, abs_of_pos (slopeOffsetScale_pos s)]
    calc
      _ ≤ (1 / 4 : ℝ) * (1 / 3) := by gcongr; exact slopeOffsetScale_le_quarter s
      _ = _ := by norm_num
  have hd' : |slopeOffsetScale s * p.d| ≤ 1 / 2 := by
    rw [abs_mul, abs_of_pos (slopeOffsetScale_pos s)]
    calc
      _ ≤ (1 / 4 : ℝ) * 2 := by gcongr; exact slopeOffsetScale_le_quarter s
      _ = _ := by norm_num
  refine ⟨?_, hb', ?_, hd'⟩
  · convert ha' using 1 <;> norm_num [slopeOffsetParams]
  · convert hc' using 1 <;> norm_num [slopeOffsetParams]

/-- The chosen horizontal shear is a contraction in the ambient Euclidean norm. -/
theorem slopeOffsetLinear_norm_le (s : ℝ) (p : Point3) :
    ‖slopeOffsetLinear s p‖ ≤ ‖p‖ := by
  have hk := (slopeOffsetScale_pos s).le
  have hks : slopeOffsetScale s * |s| ≤ 1 / 4 := by
    nlinarith [slopeOffsetScale_mul_one_add_abs s]
  have hx : |slopeOffsetLinear s p 0| ≤ (|p 0| + |p 1|) / 4 := by
    rw [slopeOffsetLinear_coord_zero, abs_mul, abs_of_pos (slopeOffsetScale_pos s)]
    calc
      _ ≤ slopeOffsetScale s * (|p 0| + |s| * |p 1|) := by
        gcongr
        simpa only [abs_mul] using abs_add_le (p 0) (s * p 1)
      _ = slopeOffsetScale s * |p 0| +
          (slopeOffsetScale s * |s|) * |p 1| := by ring
      _ ≤ (1 / 4 : ℝ) * |p 0| + (1 / 4 : ℝ) * |p 1| := by
        gcongr
        exact slopeOffsetScale_le_quarter s
      _ = _ := by ring
  have hy : |slopeOffsetLinear s p 1| ≤ |p 1| / 4 := by
    rw [slopeOffsetLinear_coord_one, abs_mul, abs_of_pos (slopeOffsetScale_pos s)]
    calc
      _ ≤ (1 / 4 : ℝ) * |p 1| := by
        gcongr
        exact slopeOffsetScale_le_quarter s
      _ = _ := by ring
  have hx2 : (slopeOffsetLinear s p 0) ^ 2 ≤ ((|p 0| + |p 1|) / 4) ^ 2 := by
    nlinarith [sq_abs (slopeOffsetLinear s p 0), abs_nonneg (slopeOffsetLinear s p 0)]
  have hy2 : (slopeOffsetLinear s p 1) ^ 2 ≤ (|p 1| / 4) ^ 2 := by
    nlinarith [sq_abs (slopeOffsetLinear s p 1), abs_nonneg (slopeOffsetLinear s p 1)]
  have hsource := point3_coord_norm_sq p
  have htarget := point3_coord_norm_sq (slopeOffsetLinear s p)
  rw [slopeOffsetLinear_coord_two] at htarget
  nlinarith [sq_abs (p 0), sq_abs (p 1), sq_nonneg (|p 0| - |p 1|),
    norm_nonneg p, norm_nonneg (slopeOffsetLinear s p)]

theorem slopeOffsetLinear_dist_le (s : ℝ) (p q : Point3) :
    dist (slopeOffsetLinear s p) (slopeOffsetLinear s q) ≤ dist p q := by
  simpa only [dist_eq_norm, map_sub] using slopeOffsetLinear_norm_le s (p - q)

/-- Horizontal scaling of the target plane. -/
def slopeOffsetTargetLinear (s : ℝ) : Point2 →ₗ[ℝ] Point2 where
  toFun p := WithLp.toLp 2 ![slopeOffsetScale s * p 0, p 1]
  map_add' p q := by ext i; fin_cases i <;> simp <;> ring
  map_smul' a p := by ext i; fin_cases i <;> simp <;> ring

/-- Centering the actual slope commutes with the spatial coordinate change. -/
theorem slopeOffset_twistedProjection (f : SlopeFunction) (p : Point3) :
    twistedProjection f.centered (slopeOffsetLinear (f 0) p) =
      slopeOffsetTargetLinear (f 0) (twistedProjection f p) := by
  ext i
  fin_cases i <;> simp [twistedProjection, slopeOffsetTargetLinear,
    SlopeFunction.centered, slopeOffsetLinear, point3, EuclideanSpace.single_apply] <;> ring

theorem slopeOffset_twisted_image (f : SlopeFunction) (E : Set Point3) :
    twistedProjection f.centered '' (slopeOffsetLinear (f 0) '' E) =
      slopeOffsetTargetLinear (f 0) '' (twistedProjection f '' E) := by
  rw [← Set.image_comp, ← Set.image_comp]
  congr 1
  funext p
  exact slopeOffset_twistedProjection f p

theorem slopeOffsetTargetLinear_det (s : ℝ) :
    LinearMap.det (slopeOffsetTargetLinear s) = slopeOffsetScale s := by
  let mat : Matrix (Fin 2) (Fin 2) ℝ := !![slopeOffsetScale s, 0; 0, 1]
  have heq : slopeOffsetTargetLinear s = Matrix.toLpLin 2 2 mat := by
    ext p i
    have hmatrix := Matrix.ofLp_toLpLin (p := (2 : ENNReal)) (q := (2 : ENNReal)) mat p
    have hi := congr_fun hmatrix i
    fin_cases i <;> simpa [slopeOffsetTargetLinear, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, mat] using hi.symm
  rw [heq, LinearMap.det_toLpLin]
  simp [mat, Matrix.det_fin_two]

/-- Exact projected-area transport; no independent image set is selected. -/
theorem slopeOffset_twisted_volume (f : SlopeFunction) (E : Set Point3) :
    volume (twistedProjection f.centered '' (slopeOffsetLinear (f 0) '' E)) =
      ENNReal.ofReal (slopeOffsetScale (f 0)) * volume (twistedProjection f '' E) := by
  rw [slopeOffset_twisted_image,
    MeasureTheory.Measure.addHaar_image_linearMap, slopeOffsetTargetLinear_det,
    abs_of_pos (slopeOffsetScale_pos _)]

end Kakeya.Assouad
end
