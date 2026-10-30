import MyLeanRepo.Kakeya.Assouad.PureWZ2.FullLineTubeWolffLowerBound
import MyLeanRepo.Kakeya.Assouad.PureWZ2.ParameterFrostmanLowerBound
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Section7Nonconcentration
import MyLeanRepo.Kakeya.Assouad.PureWZ2.BoundedDeltaMax
import MyLeanRepo.Kakeya.Assouad.EssentiallyDistinctCardBound
import MyLeanRepo.Kakeya.Assouad.ConstantAbsorption

/-!
# Section 7 lower bounds without an extremal cardinality assumption

Essential distinctness and bounded support give the elementary six-dimensional
packing bound.  The polynomial GridOS theorem therefore applies with budget
seven, after absorbing the fixed packing constant.  The CWA corollary supplies physical full-line Tube Wolff tests.  Their
projection theorem derives parameter Frostman by tube containment and
volume, spending half the source loss on the fixed geometric constant.

These are normalized vertical-chart statements for ordinary capsule shadings.
The ordinary capsule Tube-Wolff-to-full-line reduction and the general
chart/slope normalization are still absent.  The full-line test model is
explicit in the intermediate Proposition 7.1 theorem.
-/

namespace Kakeya.Assouad

/-- Normalized parameter-Frostman lower bound.  Its cardinality upper bound
is proved from essential distinctness, rather than added as a hypothesis. -/
theorem pure_wz2_parameter_frostman_lower_bound_of_essentially_distinct :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∃ eta delta₀ : ℝ,
        0 < eta ∧ eta ≤ epsilon ∧ 0 < delta₀ ∧ delta₀ < 1 ∧
        ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
          ∀ F : Kakeya.Streamlined.TubeFamily delta,
            F.Nonempty → HasBoundedBase F 4 → F.IsEssentiallyDistinct →
            IsInVerticalChart F →
            TubeParameterFrostmanBound F (Kakeya.realRpowENN delta (-eta)) →
            ∀ Y : Kakeya.Streamlined.TubeShading F,
              Y.IsLambdaDense (Kakeya.realRpowENN delta eta) →
              IsInSlopeWindow Y →
              ∀ f : SlopeFunction, f.IsNonsingular → f 0 = 0 →
                Kakeya.realRpowENN delta epsilon ≤
                  MeasureTheory.volume (twistedUnion Y f) := by
  intro epsilon hepsilon
  obtain ⟨eta, scale, heta, hetaEpsilon, _hetaOne, hscale, hscaleOne, hmain⟩ :=
    pure_wz2_proposition7_1_parameter_frostman 7 (by norm_num) epsilon hepsilon
  obtain ⟨packingScale, hpackingScale, _hpackingOne, hpacking⟩ :=
    exists_delta_mul_rpow_le_rpow ((37 * 6 : ℝ) ^ 6) (by positivity)
      (show (-7 : ℝ) < -6 by norm_num)
  let delta₀ := min scale (min packingScale (1 / 32))
  have hdelta₀ : 0 < delta₀ := by positivity
  have hdelta₀Scale : delta₀ ≤ scale := min_le_left _ _
  refine ⟨eta, delta₀, heta, hetaEpsilon, hdelta₀,
    hdelta₀Scale.trans_lt hscaleOne, ?_⟩
  intro delta hdelta hdeltaLe F hnonempty hbase hdistinct hvertical hfrostman
    Y hdense hwindow f hnonsingular hzero
  have hdeltaScale := hdeltaLe.trans hdelta₀Scale
  have hdeltaOne : delta ≤ 1 := (hdeltaScale.trans_lt hscaleOne).le
  have hdeltaSmall : delta < 1 / 16 := by
    have h : delta ≤ (1 / 32 : ℝ) :=
      hdeltaLe.trans ((min_le_right _ _).trans (min_le_right _ _))
    linarith
  have hdeltaPacking : delta ≤ packingScale :=
    hdeltaLe.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hsupport : ∀ i, (F.tube i).carrier ⊆ Metric.closedBall (0 : Point3) 6 :=
    fun i => tube_carrier_subset_closedBall_six hdelta.le hdeltaOne (F.tube i) (hbase i)
  have hcardReal : (F.card : ℝ) ≤ Real.rpow delta (-7) :=
    (essentially_distinct_card_bound_fixed_ball hdelta hdeltaOne hdeltaSmall
      (by norm_num : (1 : ℝ) ≤ 6) hsupport hdistinct).trans
        (hpacking delta hdelta hdeltaPacking)
  have hcard : F.enncard ≤ Kakeya.realRpowENN delta (-7) := by
    simpa [Kakeya.Streamlined.TubeFamily.enncard, Kakeya.realRpowENN] using
      ENNReal.ofReal_le_ofReal hcardReal
  exact hmain delta hdelta hdeltaScale F hnonempty hvertical
    (tubeParams_bounds hbase hvertical) hcard hfrostman Y hdense hwindow
    f hnonsingular hzero

/-- The normalized full-line Tube Wolff lower bound with its polynomial
cardinality budget derived from bounded support and analytic distinctness. -/
theorem pure_wz2_full_line_tube_wolff_lower_bound_in_vertical_chart :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∃ eta delta₀ : ℝ,
        0 < eta ∧ eta ≤ epsilon ∧ 0 < delta₀ ∧ delta₀ < 1 ∧
        ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
          ∀ F : Kakeya.Streamlined.TubeFamily delta,
            F.Nonempty → HasBoundedBase F 4 → F.IsEssentiallyDistinct →
            IsInVerticalChart F →
            FullLineTubeWolffBound F 6 (Kakeya.realRpowENN delta (-eta)) →
            ∀ Y : Kakeya.Streamlined.TubeShading F,
              Y.IsLambdaDense (Kakeya.realRpowENN delta eta) →
              IsInSlopeWindow Y →
              ∀ f : SlopeFunction, f.IsNonsingular → f 0 = 0 →
                Kakeya.realRpowENN delta epsilon ≤
                  MeasureTheory.volume (twistedUnion Y f) := by
  intro epsilon hepsilon
  obtain ⟨eta, scale, heta, hetaEpsilon, _hetaOne, hscale, hscaleOne, hmain⟩ :=
    pure_wz2_proposition7_1_full_line_tube_wolff 7 (by norm_num) epsilon hepsilon
  obtain ⟨packingScale, hpackingScale, _hpackingOne, hpacking⟩ :=
    exists_delta_mul_rpow_le_rpow ((37 * 6 : ℝ) ^ 6) (by positivity)
      (show (-7 : ℝ) < -6 by norm_num)
  let delta₀ := min scale (min packingScale (1 / 32))
  have hdelta₀ : 0 < delta₀ := by positivity
  have hdelta₀Scale : delta₀ ≤ scale := min_le_left _ _
  refine ⟨eta, delta₀, heta, hetaEpsilon, hdelta₀,
    hdelta₀Scale.trans_lt hscaleOne, ?_⟩
  intro delta hdelta hdeltaLe F hnonempty hbase hdistinct hvertical hfrostman
    Y hdense hwindow f hnonsingular hzero
  have hdeltaScale := hdeltaLe.trans hdelta₀Scale
  have hdeltaOne : delta ≤ 1 := (hdeltaScale.trans_lt hscaleOne).le
  have hdeltaSmall : delta < 1 / 16 := by
    have h : delta ≤ (1 / 32 : ℝ) :=
      hdeltaLe.trans ((min_le_right _ _).trans (min_le_right _ _))
    linarith
  have hdeltaPacking : delta ≤ packingScale :=
    hdeltaLe.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hsupport : ∀ i, (F.tube i).carrier ⊆ Metric.closedBall (0 : Point3) 6 :=
    fun i => tube_carrier_subset_closedBall_six hdelta.le hdeltaOne (F.tube i) (hbase i)
  have hcardReal : (F.card : ℝ) ≤ Real.rpow delta (-7) :=
    (essentially_distinct_card_bound_fixed_ball hdelta hdeltaOne hdeltaSmall
      (by norm_num : (1 : ℝ) ≤ 6) hsupport hdistinct).trans
        (hpacking delta hdelta hdeltaPacking)
  have hcard : F.enncard ≤ Kakeya.realRpowENN delta (-7) := by
    simpa [Kakeya.Streamlined.TubeFamily.enncard, Kakeya.realRpowENN] using
      ENNReal.ofReal_le_ofReal hcardReal
  exact hmain delta hdelta hdeltaScale F hnonempty hbase hvertical
    hcard hfrostman Y hdense hwindow
    f hnonsingular hzero

/-- Normalized CWA projection lower bound for the existing ordinary capsule
model.  No parameter-Frostman or cardinality premise is imposed.  The proof
actually specializes the full-line Tube Wolff projection theorem.  The
general ordinary-capsule and coordinate reductions are not asserted. -/
theorem pure_wz2_convex_wolff_lower_bound_in_vertical_chart :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∃ eta delta₀ : ℝ,
        0 < eta ∧ eta ≤ epsilon ∧ 0 < delta₀ ∧ delta₀ < 1 ∧
        ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
          ∀ F : Kakeya.Streamlined.TubeFamily delta,
            F.Nonempty → HasBoundedBase F 4 → F.IsEssentiallyDistinct →
            IsInVerticalChart F →
            ConvexWolffBound F (Kakeya.realRpowENN delta (-eta)) →
            ∀ Y : Kakeya.Streamlined.TubeShading F,
              Y.IsLambdaDense (Kakeya.realRpowENN delta eta) →
              IsInSlopeWindow Y →
              ∀ f : SlopeFunction, f.IsNonsingular → f 0 = 0 →
                Kakeya.realRpowENN delta epsilon ≤
                  MeasureTheory.volume (twistedUnion Y f) := by
  intro epsilon hepsilon
  obtain ⟨eta, delta₀, heta, hetaEpsilon, hd, hd1, lower⟩ :=
    pure_wz2_full_line_tube_wolff_lower_bound_in_vertical_chart epsilon hepsilon
  refine ⟨eta, delta₀, heta, hetaEpsilon, hd, hd1, ?_⟩
  intro delta hdelta hsmall F hn hb he hv hcwa Y hy hw f hf h0
  exact lower delta hdelta hsmall F hn hb he hv
    (fullLineTubeWolffBound_of_convexWolffBound hdelta hcwa) Y hy hw f hf h0

end Kakeya.Assouad
