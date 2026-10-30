import MyLeanRepo.Kakeya.Assouad.PureWZ2.SlopeOffsetRetubing

/-!
# Parameter Frostman implies capsule Tube Wolff for centered segments

The source segments cover fixed heights 0 and 1/8.  Containment in one
coarse capsule forces the four line parameters into a box of radius 160r.
The coarse capsule's orientation is not assumed: its vertical component
is bounded below using the endpoints of one contained fine segment.
-/

noncomputable section
open MeasureTheory Set
namespace Kakeya.Assouad

theorem ordinary_capsule_coord_diameter {r : ℝ} (hr : 0 ≤ r)
    (T : Kakeya.DeltaTube r) {p q : Point3} (hp : p ∈ T.carrier) (hq : q ∈ T.carrier)
    (j : Fin 3) : |p j - q j| ≤ |T.direction j| + 2 * r := by
  have hc : IsCompact (Kakeya.unitSegment T.base T.direction) :=
    isCompact_Icc.image (continuous_const.add (continuous_id.smul continuous_const))
  obtain ⟨a, ha, hpa⟩ := exists_dist_le_of_mem_cthickening_closed hc.isClosed hr hp
  obtain ⟨b, hb, hqb⟩ := exists_dist_le_of_mem_cthickening_closed hc.isClosed hr hq
  have hab : |a j - b j| ≤ |T.direction j| := by
    obtain ⟨u, hu, rfl⟩ := ha
    obtain ⟨v, hv, rfl⟩ := hb
    have huv : |u - v| ≤ 1 := abs_le.mpr ⟨by linarith [hu.1, hv.2], by linarith [hu.2, hv.1]⟩
    have heq : (T.base + u • T.direction) j - (T.base + v • T.direction) j =
        (u - v) * T.direction j := by simp; ring
    rw [heq, abs_mul]
    exact (mul_le_mul_of_nonneg_right huv (abs_nonneg _)).trans_eq (one_mul _)
  calc
    _ ≤ |p j - a j| + |a j - q j| := abs_sub_le _ _ _
    _ ≤ |p j - a j| + (|a j - b j| + |b j - q j|) := by
      gcongr
      exact abs_sub_le _ _ _
    _ ≤ r + (|T.direction j| + r) := by
      exact add_le_add ((abs_coord_sub_le_dist j).trans hpa)
        (add_le_add hab (by simpa only [abs_sub_comm] using
          (abs_coord_sub_le_dist (x := q) (y := b) j).trans hqb))
    _ = _ := by ring

theorem capsule_container_vertical {delta r : ℝ} (hdelta : 0 ≤ delta)
    (hr : 0 ≤ r) (hrSmall : r ≤ 1 / 8)
    (S : Kakeya.DeltaTube delta) (T : Kakeya.DeltaTube r)
    (hS : (1 / 2 : ℝ) ≤ |S.direction 2|) (hST : S.carrier ⊆ T.carrier) :
    (1 / 4 : ℝ) ≤ |T.direction 2| := by
  have hbase : S.base ∈ S.carrier := Metric.mem_cthickening_of_dist_le _ S.base _ _
    ⟨0, by norm_num, by simp⟩ (by simpa using hdelta)
  have hend : S.base + S.direction ∈ S.carrier := Metric.mem_cthickening_of_dist_le
    _ (S.base + S.direction) _ _ ⟨1, by norm_num, by simp⟩ (by simpa using hdelta)
  have h := ordinary_capsule_coord_diameter hr T (hST hend) (hST hbase) 2
  simp only [PiLp.add_apply, add_sub_cancel_left] at h
  linarith

/-- Euclidean line-neighborhood containment bounds its vertical-chart residuals. -/
theorem vertical_line_neighbourhood_residual {delta r B : ℝ}
    (hr : 0 ≤ r) (T : Kakeya.DeltaTube delta) (hv : T.direction 2 ≠ 0)
    (hc : |(tubeParamsOfTube T).c| ≤ B) (hd : |(tubeParamsOfTube T).d| ≤ B)
    {p : Point3} (hp : p ∈ Metric.cthickening r (tubeAxisLine T)) :
    |p 0 - ((tubeParamsOfTube T).a + (tubeParamsOfTube T).c * p 2)| ≤ (1 + B) * r ∧
    |p 1 - ((tubeParamsOfTube T).b + (tubeParamsOfTube T).d * p 2)| ≤ (1 + B) * r := by
  obtain ⟨q, hq, hpq⟩ := exists_dist_le_of_mem_cthickening_closed (isClosed_tubeAxisLine T) hr hp
  have hcoord (j : Fin 3) : |p j - q j| ≤ r := (abs_coord_sub_le_dist j).trans hpq
  have hres (x x' a c : ℝ) (hx : |x - x'| ≤ r)
      (hline : x' = a + c * q 2) (hc' : |c| ≤ B) :
      |x - (a + c * p 2)| ≤ (1 + B) * r := by
    have heq : x - (a + c * p 2) = (x - x') + c * (q 2 - p 2) := by rw [hline]; ring
    rw [heq]
    calc
      _ ≤ |x - x'| + |c| * |q 2 - p 2| := by
        simpa only [abs_mul] using abs_add_le (x - x') (c * (q 2 - p 2))
      _ ≤ r + B * r := add_le_add hx
        (mul_le_mul hc' (by simpa only [abs_sub_comm] using hcoord 2) (abs_nonneg _) (by linarith [abs_nonneg c]))
      _ = _ := by ring
  exact ⟨hres _ _ _ _ (hcoord 0) (tubeAxisLine_coord_zero T hv hq) hc,
    hres _ _ _ _ (hcoord 1) (tubeAxisLine_coord_one T hv hq) hd⟩

theorem tubeParameterFrostman_to_centered_tubeWolff {delta : ℝ}
    (hdelta : 0 < delta) {F : Kakeya.Streamlined.TubeFamily delta}
    (hvertical : IsInVerticalChart F)
    (hsegments : ∀ i z, |z| ≤ 1 / 8 →
      slopeOffsetAxisPoint (tubeParamsOfTube (F.tube i)) z ∈
        Kakeya.unitSegment (F.tube i).base (F.tube i).direction)
    {C : ENNReal} (hC : 1 ≤ C) (hF : TubeParameterFrostmanBound F C) :
    TubeWolffBound F (25600 * C) := by
  classical
  intro r hdr hrOne T
  have hr : 0 < r := hdelta.trans_le hdr
  let contained := F.toBodyFamily.containedIndices T.carrier
  by_cases hempty : contained.Nonempty
  · obtain ⟨reference, href⟩ := hempty
    have href' : (F.tube reference).carrier ⊆ T.carrier :=
      Kakeya.Streamlined.BodyFamily.mem_containedIndices_iff.mp href
    by_cases hsmall : r ≤ 1 / 160
    · have hvBound := capsule_container_vertical hdelta.le hr.le (by linarith)
        (F.tube reference) T (hvertical reference) href'
      have hv : T.direction 2 ≠ 0 := by intro hz; rw [hz, abs_zero] at hvBound; linarith
      have hslopes : |(tubeParamsOfTube T).c| ≤ 4 ∧ |(tubeParamsOfTube T).d| ≤ 4 := by
        have hden : 0 < |T.direction 2| := by linarith
        have hcoord (j : Fin 3) : |T.direction j| ≤ 1 := by
          simpa only [T.direction_unit, Real.norm_eq_abs] using PiLp.norm_apply_le T.direction j
        constructor
        · change |T.direction 0 / T.direction 2| ≤ 4
          rw [abs_div]
          exact (div_le_iff₀ hden).2 (by linarith [hcoord 0])
        · change |T.direction 1 / T.direction 2| ≤ 4
          rw [abs_div]
          exact (div_le_iff₀ hden).2 (by linarith [hcoord 1])
      have hres (i : Fin F.card) (hi : i ∈ contained) (z : ℝ) (hz : |z| ≤ 1 / 8) :
          |(tubeParamsOfTube (F.tube i)).a + (tubeParamsOfTube (F.tube i)).c * z -
            ((tubeParamsOfTube T).a + (tubeParamsOfTube T).c * z)| ≤ 5 * r ∧
          |(tubeParamsOfTube (F.tube i)).b + (tubeParamsOfTube (F.tube i)).d * z -
            ((tubeParamsOfTube T).b + (tubeParamsOfTube T).d * z)| ≤ 5 * r := by
        have hi' := Kakeya.Streamlined.BodyFamily.mem_containedIndices_iff.mp hi
        have hpoint := hi' (Metric.mem_cthickening_of_dist_le
          (slopeOffsetAxisPoint (tubeParamsOfTube (F.tube i)) z)
          (slopeOffsetAxisPoint (tubeParamsOfTube (F.tube i)) z) _ _
          (hsegments i z hz) (by simpa using hdelta.le))
        have haxis : slopeOffsetAxisPoint (tubeParamsOfTube (F.tube i)) z ∈
            Metric.cthickening r (tubeAxisLine T) := by
          apply Metric.cthickening_subset_of_subset r _ hpoint
          rintro q ⟨u, hu, rfl⟩
          exact ⟨u, rfl⟩
        have h := vertical_line_neighbourhood_residual hr.le T hv hslopes.1 hslopes.2 haxis
        norm_num at h
        exact h
      let cluster := Finset.univ.filter fun i : Fin F.card =>
        |(tubeParams i).a - (tubeParams reference).a| ≤ 160 * r ∧
        |(tubeParams i).b - (tubeParams reference).b| ≤ 160 * r ∧
        |(tubeParams i).c - (tubeParams reference).c| ≤ 160 * r ∧
        |(tubeParams i).d - (tubeParams reference).d| ≤ 160 * r
      have hsubset : contained ⊆ cluster := by
        intro i hi
        have h0 := hres i hi 0 (by norm_num)
        have h1 := hres i hi (1 / 8) (by norm_num)
        have hr0 := hres reference href 0 (by norm_num)
        have hr1 := hres reference href (1 / 8) (by norm_num)
        simp only [mul_zero, add_zero] at h0 hr0
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        change _ ∧ _ ∧ _ ∧ _
        simp only [tubeParams]
        constructor
        · exact abs_le.mpr ⟨by linarith [abs_le.mp h0.1, abs_le.mp hr0.1],
            by linarith [abs_le.mp h0.1, abs_le.mp hr0.1]⟩
        constructor
        · exact abs_le.mpr ⟨by linarith [abs_le.mp h0.2, abs_le.mp hr0.2],
            by linarith [abs_le.mp h0.2, abs_le.mp hr0.2]⟩
        constructor
        · exact abs_le.mpr ⟨by linarith [abs_le.mp h0.1, abs_le.mp hr0.1, abs_le.mp h1.1, abs_le.mp hr1.1],
            by linarith [abs_le.mp h0.1, abs_le.mp hr0.1, abs_le.mp h1.1, abs_le.mp hr1.1]⟩
        · exact abs_le.mpr ⟨by linarith [abs_le.mp h0.2, abs_le.mp hr0.2, abs_le.mp h1.2, abs_le.mp hr1.2],
            by linarith [abs_le.mp h0.2, abs_le.mp hr0.2, abs_le.mp h1.2, abs_le.mp hr1.2]⟩
      have hscale : Kakeya.realRpowENN (160 * r) 2 = 25600 * Kakeya.realRpowENN r 2 := by
        norm_num [Kakeya.realRpowENN, mul_pow, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 25600)]
      calc
        _ = (contained.card : ENNReal) := rfl
        _ ≤ (cluster.card : ENNReal) := by exact_mod_cast Finset.card_le_card hsubset
        _ ≤ C * Kakeya.realRpowENN (160 * r) 2 * F.enncard :=
          hF (160 * r) (by linarith) (by linarith) reference
        _ = _ := by rw [hscale]; ring
    · have hcard : (contained.card : ENNReal) ≤ F.enncard := by
        have h := Finset.card_le_card (Finset.subset_univ contained)
        have hsize : (Finset.univ : Finset (Fin F.toBodyFamily.card)).card = F.card :=
          (Finset.card_univ).trans (Fintype.card_fin F.card)
        change (contained.card : ENNReal) ≤ (F.card : ENNReal)
        exact_mod_cast h.trans_eq hsize
      have hfactor : (1 : ENNReal) ≤ 25600 * Kakeya.realRpowENN r 2 := by
        have h : (1 : ℝ) ≤ 25600 * r ^ 2 := by nlinarith
        simpa [Kakeya.realRpowENN, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 25600)] using
          ENNReal.ofReal_mono h
      calc
        _ ≤ F.enncard := hcard
        _ ≤ (25600 * Kakeya.realRpowENN r 2) * F.enncard := by
          exact (le_mul_of_one_le_left' hfactor)
        _ = (25600 * 1 * Kakeya.realRpowENN r 2) * F.enncard := by rw [mul_one]
        _ ≤ _ := by gcongr
  · have hzero : contained = ∅ := Finset.not_nonempty_iff_eq_empty.mp hempty
    change (contained.card : ENNReal) ≤ _
    rw [hzero, Finset.card_empty, Nat.cast_zero]
    positivity

end Kakeya.Assouad
end
