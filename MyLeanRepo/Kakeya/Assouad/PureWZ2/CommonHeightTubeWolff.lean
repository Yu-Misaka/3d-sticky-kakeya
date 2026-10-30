import MyLeanRepo.Kakeya.Assouad.PureWZ2.SlopeOffsetRetubing
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperUnitRescalingBasics

/-!
# Ordinary Tube Wolff for unit segments centered at one height

The actual slope-offset retubing chooses all unit segments at a common
height. For these representatives a parameter cluster fits in an ordinary
coarse unit-segment capsule. No full-line test or convex-set bound enters
the reduction. All fine indices, including multiplicities, are counted.
-/

noncomputable section
open MeasureTheory Set
namespace Kakeya.Assouad

/-- The positive vertical unit representatives have a common center height.
This is a condition on the actual segments, not only their supporting lines. -/
def HasCommonHeightTubeModel {delta : ℝ} (F : Kakeya.Streamlined.TubeFamily delta) : Prop :=
  ∃ m : ℝ, |m| ≤ 1 ∧ ∀ i,
    F.tube i = slopeOffsetModelTube (tubeParams i) m delta

private theorem norm_le_two_of_horizontal_coordinates {v : Point3} {w : ℝ}
    (hw : 0 ≤ w) (hx : |v 0| ≤ w) (hy : |v 1| ≤ w) (hz : v 2 = 0) :
    ‖v‖ ≤ 2 * w := by
  have hn := point3_coord_norm_sq v
  rw [hz] at hn
  nlinarith [sq_abs (v 0), sq_abs (v 1), abs_le.mp hx, abs_le.mp hy, norm_nonneg v]

theorem commonHeight_axisPoint_dist {p q : TubeParams} {m r : ℝ}
    (hr : 0 ≤ r) (hm : |m| ≤ 1)
    (ha : |p.a - q.a| ≤ r) (hb : |p.b - q.b| ≤ r)
    (hc : |p.c - q.c| ≤ r) (hd : |p.d - q.d| ≤ r) :
    dist (slopeOffsetAxisPoint p m) (slopeOffsetAxisPoint q m) ≤ 4 * r := by
  have coord (a b c d : ℝ) (hab : |a - b| ≤ r) (hcd : |c - d| ≤ r) :
      |(a + c * m) - (b + d * m)| ≤ 2 * r := by
    rw [show (a + c * m) - (b + d * m) = (a - b) + (c - d) * m by ring]
    calc
      _ ≤ |a - b| + |c - d| * |m| := by simpa only [abs_mul] using abs_add_le (a-b) ((c-d)*m)
      _ ≤ r + r * 1 := by gcongr
      _ = _ := by ring
  rw [dist_eq_norm]
  have h := norm_le_two_of_horizontal_coordinates (w := 2 * r) (by positivity)
    (by simpa using coord p.a q.a p.c q.c ha hc)
    (by simpa using coord p.b q.b p.d q.d hb hd)
    (show (slopeOffsetAxisPoint p m - slopeOffsetAxisPoint q m) 2 = 0 by simp)
  linarith

theorem commonHeight_direction_dist {p q : TubeParams} {r : ℝ}
    (hr : 0 ≤ r) (hc : |p.c - q.c| ≤ r) (hd : |p.d - q.d| ≤ r) :
    dist (slopeOffsetUnitDirection p) (slopeOffsetUnitDirection q) ≤ 2 * r := by
  have hnorm (s : TubeParams) : 1 ≤ ‖slopeOffsetAxisVector s‖ := by
    simpa using PiLp.norm_apply_le (slopeOffsetAxisVector s) (2 : Fin 3)
  have hsub : ‖slopeOffsetAxisVector p - slopeOffsetAxisVector q‖ ≤ 2 * r :=
    norm_le_two_of_horizontal_coordinates hr (by simpa using hc)
      (by simpa using hd) (by simp)
  exact (norm_normalize_sub_normalize_le_norm_sub (hnorm p) (hnorm q)).trans hsub

/-- Corresponding points on the actual unit segments are uniformly close. -/
theorem commonHeight_segment_point_dist {p q : TubeParams} {m r t : ℝ}
    (hr : 0 ≤ r) (hm : |m| ≤ 1) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (ha : |p.a - q.a| ≤ r) (hb : |p.b - q.b| ≤ r)
    (hc : |p.c - q.c| ≤ r) (hd : |p.d - q.d| ≤ r) (delta R : ℝ) :
    dist ((slopeOffsetModelTube p m delta).base + t • (slopeOffsetModelTube p m delta).direction)
      ((slopeOffsetModelTube q m R).base + t • (slopeOffsetModelTube q m R).direction) ≤
        5 * r := by
  have hpoint := commonHeight_axisPoint_dist hr hm ha hb hc hd
  have hdirection := commonHeight_direction_dist hr hc hd
  have ht' : |t - 1 / 2| ≤ (1 / 2 : ℝ) := abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have heq :
      ((slopeOffsetModelTube p m delta).base + t • (slopeOffsetModelTube p m delta).direction) -
        ((slopeOffsetModelTube q m R).base + t • (slopeOffsetModelTube q m R).direction) =
      (slopeOffsetAxisPoint p m - slopeOffsetAxisPoint q m) +
        (t - 1 / 2) • (slopeOffsetUnitDirection p - slopeOffsetUnitDirection q) := by
    dsimp only [slopeOffsetModelTube]
    module
  rw [dist_eq_norm, heq]
  calc
    _ ≤ ‖slopeOffsetAxisPoint p m - slopeOffsetAxisPoint q m‖ +
        ‖(t - 1 / 2) • (slopeOffsetUnitDirection p - slopeOffsetUnitDirection q)‖ := norm_add_le _ _
    _ ≤ 4 * r + (1 / 2) * (2 * r) := by
      rw [norm_smul, Real.norm_eq_abs]
      exact add_le_add hpoint (mul_le_mul ht' hdirection (norm_nonneg _) (by norm_num))
    _ = _ := by ring

/-- A parameter cluster is contained in a single ordinary coarse capsule. -/
theorem commonHeight_modelTube_carrier_subset {p q : TubeParams} {m delta r : ℝ}
    (hdelta : 0 ≤ delta) (hdr : delta ≤ r) (hm : |m| ≤ 1)
    (ha : |p.a - q.a| ≤ r) (hb : |p.b - q.b| ≤ r)
    (hc : |p.c - q.c| ≤ r) (hd : |p.d - q.d| ≤ r) :
    (slopeOffsetModelTube p m delta).carrier ⊆ (slopeOffsetModelTube q m (8 * r)).carrier := by
  intro x hx
  have hcompact : IsCompact (Kakeya.unitSegment
      (slopeOffsetModelTube p m delta).base (slopeOffsetModelTube p m delta).direction) :=
    isCompact_Icc.image (continuous_const.add (continuous_id.smul continuous_const))
  obtain ⟨y, ⟨t, ht, rfl⟩, hxy⟩ :=
    exists_dist_le_of_mem_cthickening_closed hcompact.isClosed hdelta hx
  let z := (slopeOffsetModelTube q m (8 * r)).base + t • (slopeOffsetModelTube q m (8 * r)).direction
  have hz : z ∈ Kakeya.unitSegment (slopeOffsetModelTube q m (8 * r)).base
      (slopeOffsetModelTube q m (8 * r)).direction := ⟨t, ht, rfl⟩
  apply Metric.mem_cthickening_of_dist_le x z (8 * r) _ hz
  have hyz := commonHeight_segment_point_dist (hdelta.trans hdr) hm ht ha hb hc hd delta (8*r)
  have htriangle := dist_triangle x
    ((slopeOffsetModelTube p m delta).base + t • (slopeOffsetModelTube p m delta).direction) z
  change dist _ z ≤ 5 * r at hyz
  linarith

/-- Indexed parameter Frostman follows from ordinary capsule Tube Wolff
on the common-height representatives, with the fixed factor 64. -/
theorem tubeParameterFrostmanBound_of_commonHeightTubeWolffBound
    {delta : ℝ} (hdelta : 0 < delta)
    {F : Kakeya.Streamlined.TubeFamily delta} (hmodel : HasCommonHeightTubeModel F)
    {C : ENNReal} (hC : 1 ≤ C) (hwolff : TubeWolffBound F C) :
    TubeParameterFrostmanBound F (64 * C) := by
  classical
  obtain ⟨m, hm, hmodel⟩ := hmodel
  intro r hdr hrOne reference
  have hr : 0 < r := hdelta.trans_le hdr
  let indices := Finset.univ.filter fun i : Fin F.card =>
    |(tubeParams i).a - (tubeParams reference).a| ≤ r ∧
    |(tubeParams i).b - (tubeParams reference).b| ≤ r ∧
    |(tubeParams i).c - (tubeParams reference).c| ≤ r ∧
    |(tubeParams i).d - (tubeParams reference).d| ≤ r
  change (indices.card : ENNReal) ≤ _
  by_cases hsmall : r ≤ 1 / 8
  · let coarse := slopeOffsetModelTube (tubeParams reference) m (8 * r)
    have hsubset : indices ⊆ F.toBodyFamily.containedIndices coarse.carrier := by
      intro i hi
      apply Kakeya.Streamlined.BodyFamily.mem_containedIndices_iff.mpr
      change (F.tube i).carrier ⊆ coarse.carrier
      rw [hmodel i]
      obtain ⟨ha, hb, hc, hd⟩ := (Finset.mem_filter.mp hi).2
      exact commonHeight_modelTube_carrier_subset hdelta.le hdr hm ha hb hc hd
    have hpower : Kakeya.realRpowENN (8 * r) 2 = 64 * Kakeya.realRpowENN r 2 := by
      have h8 : Real.rpow (8 * r) 2 = (8 * r) ^ 2 := Real.rpow_two _
      have h1 : Real.rpow r 2 = r ^ 2 := Real.rpow_two _
      simp only [Kakeya.realRpowENN, h8, h1]
      rw [show (8*r)^2 = 64*r^2 by ring, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 64)]
      norm_num
    calc
      _ ≤ F.toBodyFamily.containedCount coarse.carrier := by
        change (indices.card : ENNReal) ≤
          ((F.toBodyFamily.containedIndices coarse.carrier).card : ENNReal)
        exact_mod_cast Finset.card_le_card hsubset
      _ ≤ C * Kakeya.realRpowENN (8*r) 2 * F.enncard :=
        hwolff (8*r) (by linarith) (by linarith) coarse
      _ = _ := by rw [hpower]; ring
  · have hcount : (indices.card : ENNReal) ≤ F.enncard := by
      have h := Finset.card_le_card (Finset.subset_univ indices)
      simpa [Kakeya.Streamlined.TubeFamily.enncard] using
        (show (indices.card : ENNReal) ≤ ((Finset.univ : Finset (Fin F.card)).card : ENNReal) by exact_mod_cast h)
    have hfactor : (1 : ENNReal) ≤ 64 * Kakeya.realRpowENN r 2 := by
      have hreal : (1 : ℝ) ≤ 64 * r ^ 2 := by nlinarith
      simpa [Kakeya.realRpowENN, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 64)] using
        ENNReal.ofReal_mono hreal
    calc
      _ ≤ F.enncard := hcount
      _ = 1 * F.enncard := (one_mul _).symm
      _ ≤ (64 * Kakeya.realRpowENN r 2) * F.enncard := mul_le_mul_left hfactor _
      _ ≤ _ := by
        calc
          _ = (64 * 1 * Kakeya.realRpowENN r 2) * F.enncard := by rw [mul_one]
          _ ≤ _ := by gcongr

end Kakeya.Assouad
end
