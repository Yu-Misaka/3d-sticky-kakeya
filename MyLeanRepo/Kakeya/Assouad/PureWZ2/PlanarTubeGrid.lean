import MyLeanRepo.Kakeya.Assouad.PureWZ2.SlopeOffsetObstructionGeometry
import Mathlib.Order.Interval.Finset.Fin

/-!
# A finite two-parameter grid of lines in a steep plane

The lines x=a+c*z, y=-(a+c*z)/s have uniformly bounded parameters and
lie in x+s*y=0.  The a,c coordinates form an ordinary delta-grid.  Thus
the indexed line parameters satisfy a dimension-two Frostman condition
with an absolute constant, independently of the slope offset s.
-/

noncomputable section
open MeasureTheory Set
namespace Kakeya.Assouad

def planarTubeGridMesh (n : ℕ) : ℝ := (64 * (n : ℝ))⁻¹

theorem planarTubeGridMesh_pos {n : ℕ} (hn : 0 < n) : 0 < planarTubeGridMesh n := by
  unfold planarTubeGridMesh
  positivity

theorem planarTubeGridMesh_le {n : ℕ} (hn : 0 < n) : planarTubeGridMesh n ≤ 1 / 64 := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  unfold planarTubeGridMesh
  rw [← one_div]
  apply (div_le_iff₀ (by positivity)).2
  linarith

theorem planarTubeGridMesh_mul (n : ℕ) (hn : 0 < n) :
    planarTubeGridMesh n * (n : ℝ) = 1 / 64 := by
  unfold planarTubeGridMesh
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp

/-- Fine radius is 1/64 of the line-parameter grid spacing. -/
def planarTubeGridScale (n : ℕ) : ℝ := planarTubeGridMesh n / 64

theorem planarTubeGridScale_pos {n : ℕ} (hn : 0 < n) : 0 < planarTubeGridScale n := by
  exact div_pos (planarTubeGridMesh_pos hn) (by norm_num)

theorem planarTubeGridScale_le {n : ℕ} (hn : 0 < n) : planarTubeGridScale n ≤ 1 / 4096 := by
  dsimp only [planarTubeGridScale]
  linarith [planarTubeGridMesh_le hn]

theorem planarTubeGridScale_mul (n : ℕ) (hn : 0 < n) :
    planarTubeGridScale n * (n : ℝ) = 1 / 4096 := by
  dsimp only [planarTubeGridScale]
  nlinarith [planarTubeGridMesh_mul n hn]

def planarTubeGridParams (n : ℕ) (s : ℝ) (i : Fin n × Fin n) : TubeParams where
  a := planarTubeGridMesh n * (i.1 : ℝ)
  b := -(planarTubeGridMesh n * (i.1 : ℝ)) / s
  c := planarTubeGridMesh n * (i.2 : ℝ)
  d := -(planarTubeGridMesh n * (i.2 : ℝ)) / s

def planarTubeGrid (n : ℕ) (s : ℝ) : Kakeya.Streamlined.TubeFamily (planarTubeGridScale n) where
  card := n * n
  tube i := slopeOffsetModelTube
    (planarTubeGridParams n s (finProdFinEquiv.symm i)) 0 (planarTubeGridScale n)

theorem planarTubeGrid_nonempty {n : ℕ} (hn : 0 < n) (s : ℝ) :
    (planarTubeGrid n s).Nonempty := Nat.mul_pos hn hn

theorem planarTubeGrid_coordinate_bounds {n : ℕ} (hn : 0 < n) (i : Fin n) :
    0 ≤ planarTubeGridMesh n * (i : ℝ) ∧
      planarTubeGridMesh n * (i : ℝ) ≤ 1 / 64 := by
  have hi : (i : ℝ) ≤ n := by exact_mod_cast i.isLt.le
  have hδ := planarTubeGridMesh_pos hn
  refine ⟨by positivity, ?_⟩
  calc
    _ ≤ planarTubeGridMesh n * (n : ℝ) := by gcongr
    _ = _ := planarTubeGridMesh_mul n hn

theorem planarTubeGridParams_bounds {n : ℕ} (hn : 0 < n)
    {s : ℝ} (hs : 1 ≤ s) (i : Fin n × Fin n) :
    |(planarTubeGridParams n s i).a| ≤ 1 / 64 ∧
    |(planarTubeGridParams n s i).b| ≤ 1 / 64 ∧
    |(planarTubeGridParams n s i).c| ≤ 1 / 64 ∧
    |(planarTubeGridParams n s i).d| ≤ 1 / 64 := by
  have hfirst := planarTubeGrid_coordinate_bounds hn i.1
  have hsecond := planarTubeGrid_coordinate_bounds hn i.2
  have hspos : 0 < s := by linarith
  have hquot (x : ℝ) (hx : 0 ≤ x) (hx' : x ≤ 1 / 64) : |(-x) / s| ≤ 1 / 64 := by
    rw [abs_div, abs_neg, abs_of_nonneg hx, abs_of_pos hspos]
    apply (div_le_iff₀ hspos).2
    linarith
  exact ⟨by simpa [planarTubeGridParams, abs_of_nonneg hfirst.1] using hfirst.2,
    hquot _ hfirst.1 hfirst.2,
    by simpa [planarTubeGridParams, abs_of_nonneg hsecond.1] using hsecond.2,
    hquot _ hsecond.1 hsecond.2⟩

theorem planarTubeGrid_lineClass {n : ℕ} (hn : 0 < n)
    {s : ℝ} (hs : 1 ≤ s) : WZ1PaperIsLineClass (planarTubeGrid n s) := by
  intro i
  have h := planarTubeGridParams_bounds hn hs (finProdFinEquiv.symm i)
  exact slopeOffsetModelTube_lineClass _ _ _ (h.1.trans (by norm_num))
    (h.2.1.trans (by norm_num)) (h.2.2.1.trans (by norm_num)) (h.2.2.2.trans (by norm_num))

theorem planarTubeGrid_boundedBase {n : ℕ} (hn : 0 < n)
    {s : ℝ} (hs : 1 ≤ s) : HasBoundedBase (planarTubeGrid n s) 4 := by
  intro i
  have h := planarTubeGridParams_bounds hn hs (finProdFinEquiv.symm i)
  exact slopeOffsetModelTube_base_bound _ _ _ (h.1.trans (by norm_num))
    (h.2.1.trans (by norm_num)) (h.2.2.1.trans (by norm_num))
    (h.2.2.2.trans (by norm_num)) (by norm_num)

theorem planarTubeGrid_params (n : ℕ) (s : ℝ) (i : Fin (n * n)) :
    tubeParamsOfTube ((planarTubeGrid n s).tube i) =
      planarTubeGridParams n s (finProdFinEquiv.symm i) :=
  slopeOffsetModelTube_params _ _ _

theorem planarTubeGrid_axis_plane {n : ℕ} (hn : 0 < n)
    {s : ℝ} (hs : 1 ≤ s) (i : Fin (n * n)) (q : Point3)
    (hq : q ∈ tubeAxisLine ((planarTubeGrid n s).tube i)) : q 0 + s * q 1 = 0 := by
  have hline := planarTubeGrid_lineClass hn hs i
  have hv : ((planarTubeGrid n s).tube i).direction 2 ≠ 0 := by
    intro hz
    have h := hline.vertical
    rw [hz, abs_zero] at h
    norm_num at h
  have hx := tubeAxisLine_coord_zero _ hv hq
  have hy := tubeAxisLine_coord_one _ hv hq
  rw [planarTubeGrid_params] at hx hy
  rw [hx, hy]
  simp only [planarTubeGridParams]
  have hsne : s ≠ 0 := by linarith
  field_simp
  ring

/-- An interval of radius r contains at most 3r/delta points of a delta-grid. -/
theorem fin_grid_interval_count_mul {n : ℕ} {delta r : ℝ}
    (hdelta : 0 < delta) (hdr : delta ≤ r) (reference : Fin n) :
    delta * (((Finset.univ.filter fun i : Fin n =>
      |delta * (i : ℝ) - delta * (reference : ℝ)| ≤ r).card : ℕ) : ℝ) ≤ 3 * r := by
  classical
  let indices := Finset.univ.filter fun i : Fin n =>
    |delta * (i : ℝ) - delta * (reference : ℝ)| ≤ r
  have hnonempty : indices.Nonempty :=
    ⟨reference, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp; linarith⟩⟩
  let low := indices.min' hnonempty
  let high := indices.max' hnonempty
  have hlow := indices.min'_mem hnonempty
  have hhigh := indices.max'_mem hnonempty
  have hle : low ≤ high := indices.min'_le _ hhigh
  have hsubset : indices ⊆ Finset.Icc low high := by
    intro i hi
    exact Finset.mem_Icc.mpr ⟨indices.min'_le _ hi, indices.le_max' _ hi⟩
  have hcard : indices.card ≤ high.val + 1 - low.val := by
    simpa only [Fin.card_Icc] using Finset.card_le_card hsubset
  have hcardReal : (indices.card : ℝ) ≤ (high : ℝ) + 1 - (low : ℝ) := by
    have hnat : low.val ≤ high.val + 1 := by exact le_trans hle (Nat.le_succ _)
    have hreal : (indices.card : ℝ) ≤ ((high.val + 1 - low.val : ℕ) : ℝ) := by
      exact_mod_cast hcard
    simpa only [Nat.cast_sub hnat, Nat.cast_add, Nat.cast_one] using hreal
  have hl : |delta * (low : ℝ) - delta * (reference : ℝ)| ≤ r :=
    (Finset.mem_filter.mp hlow).2
  have hh : |delta * (high : ℝ) - delta * (reference : ℝ)| ≤ r :=
    (Finset.mem_filter.mp hhigh).2
  change delta * (indices.card : ℝ) ≤ 3 * r
  nlinarith [abs_le.mp hl, abs_le.mp hh]

theorem planarTubeGrid_coordinate_count {n : ℕ} (hn : 0 < n)
    {r : ℝ} (hdr : planarTubeGridScale n ≤ r) (reference : Fin n) :
    (((Finset.univ.filter fun i : Fin n =>
      |planarTubeGridMesh n * (i : ℝ) - planarTubeGridMesh n * (reference : ℝ)| ≤ r).card : ℕ) : ℝ) ≤
        12288 * (n : ℝ) * r := by
  classical
  let indices := Finset.univ.filter fun i : Fin n =>
    |planarTubeGridMesh n * (i : ℝ) - planarTubeGridMesh n * (reference : ℝ)| ≤ r
  let wider := Finset.univ.filter fun i : Fin n =>
    |planarTubeGridMesh n * (i : ℝ) - planarTubeGridMesh n * (reference : ℝ)| ≤ 64 * r
  have hr : 0 < r := (planarTubeGridScale_pos hn).trans_le hdr
  have hsubset : indices ⊆ wider := by
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2.trans (by linarith)⟩
  have hwide := fin_grid_interval_count_mul (planarTubeGridMesh_pos hn)
    (show planarTubeGridMesh n ≤ 64 * r by
      dsimp only [planarTubeGridScale] at hdr
      linarith) reference
  have hcard : (indices.card : ℝ) ≤ (wider.card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsubset
  have hmass : planarTubeGridMesh n * (indices.card : ℝ) ≤ 192 * r := by
    exact (mul_le_mul_of_nonneg_left hcard (planarTubeGridMesh_pos hn).le).trans (by
      change planarTubeGridMesh n * (wider.card : ℝ) ≤ 3 * (64 * r) at hwide
      linarith)
  have hscale : (64 * (n : ℝ)) * planarTubeGridMesh n = 1 := by
    nlinarith [planarTubeGridMesh_mul n hn]
  calc
    _ = (64 * (n : ℝ)) * (planarTubeGridMesh n * (indices.card : ℝ)) := by
      rw [← mul_assoc, hscale, one_mul]
    _ ≤ (64 * (n : ℝ)) * (192 * r) := mul_le_mul_of_nonneg_left hmass (by positivity)
    _ = _ := by ring

/-- Uniform indexed two-dimensional Frostman counting, independent of s. -/
theorem planarTubeGrid_parameter_frostman {n : ℕ} (hn : 0 < n) (s : ℝ) :
    TubeParameterFrostmanBound (planarTubeGrid n s) 150994944 := by
  classical
  intro r hdr hrOne reference
  have hr : 0 < r := (planarTubeGridScale_pos hn).trans_le hdr
  let pair : Fin (n * n) → Fin n × Fin n := finProdFinEquiv.symm
  let first := Finset.univ.filter fun i : Fin n =>
    |planarTubeGridMesh n * (i : ℝ) - planarTubeGridMesh n * ((pair reference).1 : ℝ)| ≤ r
  let second := Finset.univ.filter fun i : Fin n =>
    |planarTubeGridMesh n * (i : ℝ) - planarTubeGridMesh n * ((pair reference).2 : ℝ)| ≤ r
  let indices := Finset.univ.filter fun i : Fin (n * n) =>
    |(tubeParamsOfTube ((planarTubeGrid n s).tube i)).a -
      (tubeParamsOfTube ((planarTubeGrid n s).tube reference)).a| ≤ r ∧
    |(tubeParamsOfTube ((planarTubeGrid n s).tube i)).b -
      (tubeParamsOfTube ((planarTubeGrid n s).tube reference)).b| ≤ r ∧
    |(tubeParamsOfTube ((planarTubeGrid n s).tube i)).c -
      (tubeParamsOfTube ((planarTubeGrid n s).tube reference)).c| ≤ r ∧
    |(tubeParamsOfTube ((planarTubeGrid n s).tube i)).d -
      (tubeParamsOfTube ((planarTubeGrid n s).tube reference)).d| ≤ r
  change (indices.card : ENNReal) ≤ _
  have hsubset : indices.image pair ⊆ first.product second := by
    rintro ij hij
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hij
    have hnear := (Finset.mem_filter.mp hi).2
    simp only [planarTubeGrid_params, planarTubeGridParams] at hnear
    exact Finset.mem_product.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnear.1⟩,
       Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnear.2.2.1⟩⟩
  have hcard : indices.card ≤ first.card * second.card := by
    have h := Finset.card_le_card hsubset
    have hproduct : (first.product second).card = first.card * second.card :=
      Finset.card_product first second
    rw [Finset.card_image_of_injective _ finProdFinEquiv.symm.injective, hproduct] at h
    exact h
  have hfirst : (first.card : ℝ) ≤ 12288 * (n : ℝ) * r :=
    planarTubeGrid_coordinate_count hn hdr (pair reference).1
  have hsecond : (second.card : ℝ) ≤ 12288 * (n : ℝ) * r :=
    planarTubeGrid_coordinate_count hn hdr (pair reference).2
  have hreal : (indices.card : ℝ) ≤ 150994944 * r ^ 2 * ((n * n : ℕ) : ℝ) := by
    calc
      _ ≤ (first.card : ℝ) * (second.card : ℝ) := by exact_mod_cast hcard
      _ ≤ (12288 * (n : ℝ) * r) * (12288 * (n : ℝ) * r) := by gcongr
      _ = _ := by push_cast; ring
  have h := ENNReal.ofReal_mono hreal
  rw [ENNReal.ofReal_mul (by positivity : 0 ≤ 150994944 * r ^ 2),
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 150994944)] at h
  simpa [Kakeya.realRpowENN, Kakeya.Streamlined.TubeFamily.enncard, planarTubeGrid] using h

def planarTubeGridShading (n : ℕ) (s : ℝ) :
    Kakeya.Streamlined.TubeShading (planarTubeGrid n s) where
  carrier i := ((planarTubeGrid n s).tube i).carrier
  measurable_carrier i := Metric.isClosed_cthickening.measurableSet
  subset_body i := Set.Subset.refl _

theorem planarTubeGridShading_dense (n : ℕ) (s : ℝ) :
    (planarTubeGridShading n s).IsLambdaDense 1 := by
  change 1 * (∑ i : Fin (n * n), volume ((planarTubeGrid n s).tube i).carrier) ≤ _
  rw [one_mul]
  exact le_rfl

theorem slopeOffsetModelTube_zero_height_window (p : TubeParams)
    {delta : ℝ} (hdelta : 0 ≤ delta) (hsmall : delta ≤ 1 / 2) :
    (slopeOffsetModelTube p 0 delta).carrier ⊆ horizontalSlab (-1) 1 := by
  intro q hq
  let T := slopeOffsetModelTube p 0 delta
  have hc : IsCompact (Kakeya.unitSegment T.base T.direction) :=
    isCompact_Icc.image (continuous_const.add (continuous_id.smul continuous_const))
  obtain ⟨a, ha, hqa⟩ := exists_dist_le_of_mem_cthickening_closed hc.isClosed hdelta hq
  obtain ⟨t, ht, rfl⟩ := ha
  have ht' : |t - 1 / 2| ≤ 1 / 2 := abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hv : |T.direction 2| ≤ 1 := by
    simpa only [T.direction_unit, Real.norm_eq_abs] using PiLp.norm_apply_le T.direction 2
  have hheight : (T.base + t • T.direction) 2 = (t - 1 / 2) * T.direction 2 := by
    simp [T, slopeOffsetModelTube, PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply]
    ring
  have habs : |(T.base + t • T.direction) 2| ≤ 1 / 2 := by
    rw [hheight, abs_mul]
    calc
      _ ≤ (1 / 2 : ℝ) * 1 := by gcongr
      _ = _ := by norm_num
  have herr := (abs_coord_sub_le_dist (x := q) (y := T.base + t • T.direction) 2).trans hqa
  have hcoord : |q 2| ≤ 1 := by
    calc
      _ = |(q 2 - (T.base + t • T.direction) 2) + (T.base + t • T.direction) 2| := by ring_nf
      _ ≤ |q 2 - (T.base + t • T.direction) 2| + |(T.base + t • T.direction) 2| :=
        abs_add_le _ _
      _ ≤ delta + 1 / 2 := add_le_add herr habs
      _ ≤ 1 := by linarith
  exact abs_le.mp hcoord

theorem planarTubeGridShading_window {n : ℕ} (hn : 0 < n) (s : ℝ) :
    IsInSlopeWindow (planarTubeGridShading n s) := by
  rintro p ⟨i, hi⟩
  exact slopeOffsetModelTube_zero_height_window _ (planarTubeGridScale_pos hn).le
    ((planarTubeGridScale_le hn).trans (by norm_num)) hi

theorem planarTubeGrid_projection_volume {n : ℕ} (hn : 0 < n)
    {s : ℝ} (hs : 1 ≤ s) :
    volume (twistedUnion (planarTubeGridShading n s) (offsetObstructionSlope s)) ≤
      ENNReal.ofReal (12 * s * planarTubeGridScale n + 20 / s) :=
  offsetObstruction_projection_volume_le (planarTubeGridScale_pos hn).le
    (planarTubeGrid_boundedBase hn hs) (planarTubeGridShading n s)
    (planarTubeGridShading_window hn s) hs (planarTubeGrid_axis_plane hn hs)

end Kakeya.Assouad
end
