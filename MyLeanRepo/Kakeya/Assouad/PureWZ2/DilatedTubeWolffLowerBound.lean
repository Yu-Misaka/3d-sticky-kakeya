import MyLeanRepo.Kakeya.Assouad.PureWZ2.ParameterFrostmanLowerBound
import MyLeanRepo.Kakeya.Assouad.PureWZ2.DilatedTubeWolff
import MyLeanRepo.Kakeya.Assouad.PureWZ2.BoundedDeltaMax
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.WZ2EDSeparation
import MyLeanRepo.Kakeya.Assouad.ProjectionNormalization
import MyLeanRepo.Kakeya.Assouad.EssentiallyDistinctCardBound
import MyLeanRepo.Kakeya.Assouad.ConstantAbsorption

/-!
# Projection bounds from finite coarse capsules with longitudinal margin

Coarse tests have axis length 32. Fine tubes keep their original unit
segments and may have arbitrary longitudinal positions. The indexed
parameter bound follows from geometric capsule containment; no common-
height model or full-line projection theorem is assumed.

This explicit correction of the coarse tests is supplied directly by CWA.
It is not identified with the literal unit-length Tube Wolff hypothesis.
-/

namespace Kakeya.Assouad

/-- Normalized Proposition 7.1 for finite length-32 coarse capsules. All
losses and cutoffs precede the fine family and its longitudinal positions. -/
theorem pure_wz2_proposition7_1_dilated_tube_wolff
    (cardExponent : ℝ) (hcardExponent : 0 < cardExponent) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∃ eta delta₀ : ℝ,
        0 < eta ∧ eta ≤ epsilon ∧ eta ≤ 1 ∧ 0 < delta₀ ∧ delta₀ < 1 ∧
        ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
          ∀ F : Kakeya.Streamlined.TubeFamily delta,
            F.Nonempty → HasBoundedBase F 4 → IsInVerticalChart F →
            F.enncard ≤ Kakeya.realRpowENN delta (-cardExponent) →
            DilatedTubeWolffVolumeBound F 32 (Kakeya.realRpowENN delta (-eta)) →
            ∀ Y : Kakeya.Streamlined.TubeShading F,
              Y.IsLambdaDense (Kakeya.realRpowENN delta eta) →
              IsInSlopeWindow Y →
              ∀ f : SlopeFunction, f.IsNonsingular → f 0 = 0 →
                Kakeya.realRpowENN delta epsilon ≤
                  MeasureTheory.volume (twistedUnion Y f) := by
  intro epsilon hepsilon
  obtain ⟨sourceEta, scale, heta, hetaEpsilon, hetaOne, hscale, hscaleOne, hmain⟩ :=
    pure_wz2_proposition7_1_parameter_frostman cardExponent hcardExponent epsilon hepsilon
  obtain ⟨absorbScale, habsorbScale, _, habsorb⟩ :=
    exists_delta_mul_rpow_le_rpow 128000 (by norm_num)
      (show -sourceEta < -(sourceEta / 2) by linarith)
  let eta := sourceEta / 2
  let delta₀ := min scale absorbScale
  refine ⟨eta, delta₀, by dsimp [eta]; linarith,
    by dsimp [eta]; linarith, by dsimp [eta]; linarith,
    lt_min hscale habsorbScale, (min_le_left _ _).trans_lt hscaleOne, ?_⟩
  intro delta hdelta hdeltaLe F hnonempty hbase hvertical hcard hwolff
    Y hdense hwindow f hnonsingular hzero
  have hdeltaScale : delta ≤ scale := hdeltaLe.trans (min_le_left _ _)
  have hdeltaAbsorb : delta ≤ absorbScale := hdeltaLe.trans (min_le_right _ _)
  have hdeltaOne : delta ≤ 1 := (hdeltaScale.trans_lt hscaleOne).le
  have hCOne : 1 ≤ Kakeya.realRpowENN delta (-eta) := by
    have h := Real.rpow_le_rpow_of_exponent_ge hdelta hdeltaOne
      (show -eta ≤ 0 by dsimp [eta]; linarith)
    simpa [Kakeya.realRpowENN] using ENNReal.ofReal_mono h
  have hconstant : 128000 * Kakeya.realRpowENN delta (-eta) ≤
      Kakeya.realRpowENN delta (-sourceEta) := by
    have h := ENNReal.ofReal_le_ofReal (habsorb delta hdelta hdeltaAbsorb)
    simpa [eta, Kakeya.realRpowENN,
      ENNReal.ofReal_mul (show (0 : ℝ) ≤ 128000 by norm_num)] using h
  have hfrostman : TubeParameterFrostmanBound F
      (Kakeya.realRpowENN delta (-sourceEta)) := by
    intro r hdeltaR hrOne reference
    exact (tubeParameterFrostmanBound_of_dilatedTubeWolffBound hdelta
      hbase hvertical hCOne hwolff r hdeltaR hrOne reference).trans (by gcongr)
  have hdensityPower : Kakeya.realRpowENN delta sourceEta ≤
      Kakeya.realRpowENN delta eta :=
    ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_ge hdelta hdeltaOne
      (by dsimp [eta]; linarith))
  have hdense' : Y.IsLambdaDense (Kakeya.realRpowENN delta sourceEta) :=
    (mul_le_mul_left hdensityPower _).trans hdense
  exact hmain delta hdelta hdeltaScale F hnonempty hvertical
    (tubeParams_bounds hbase hvertical) hcard hfrostman Y hdense'
    hwindow f hnonsingular hzero

/-- The analytic packing bound removes the polynomial budget. -/
theorem pure_wz2_dilated_tube_wolff_lower_bound_in_vertical_chart :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∃ eta delta₀ : ℝ,
        0 < eta ∧ eta ≤ epsilon ∧ 0 < delta₀ ∧ delta₀ < 1 ∧
        ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
          ∀ F : Kakeya.Streamlined.TubeFamily delta,
            F.Nonempty → HasBoundedBase F 4 → F.IsEssentiallyDistinct →
            IsInVerticalChart F →
            DilatedTubeWolffVolumeBound F 32 (Kakeya.realRpowENN delta (-eta)) →
            ∀ Y : Kakeya.Streamlined.TubeShading F,
              Y.IsLambdaDense (Kakeya.realRpowENN delta eta) →
              IsInSlopeWindow Y →
              ∀ f : SlopeFunction, f.IsNonsingular → f 0 = 0 →
                Kakeya.realRpowENN delta epsilon ≤
                  MeasureTheory.volume (twistedUnion Y f) := by
  intro epsilon hepsilon
  obtain ⟨eta, scale, heta, hetaEpsilon, _hetaOne, hscale, hscaleOne, hmain⟩ :=
    pure_wz2_proposition7_1_dilated_tube_wolff 7 (by norm_num) epsilon hepsilon
  obtain ⟨packingScale, hpackingScale, _hpackingOne, hpacking⟩ :=
    exists_delta_mul_rpow_le_rpow ((37 * 6 : ℝ) ^ 6) (by positivity)
      (show (-7 : ℝ) < -6 by norm_num)
  let delta₀ := min scale (min packingScale (1 / 32))
  have hdelta₀ : 0 < delta₀ := by positivity
  have hdelta₀Scale : delta₀ ≤ scale := min_le_left _ _
  refine ⟨eta, delta₀, heta, hetaEpsilon, hdelta₀,
    hdelta₀Scale.trans_lt hscaleOne, ?_⟩
  intro delta hdelta hdeltaLe F hnonempty hbase hdistinct hvertical hwolff
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
    hcard hwolff Y hdense hwindow f hnonsingular hzero

/-- CWA supplies finite coarse tests with a longitudinal margin on any
bounded vertical-chart family, without a common-height assumption. -/
theorem pure_wz2_convex_wolff_lower_bound_via_dilated_tubes :
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
    pure_wz2_dilated_tube_wolff_lower_bound_in_vertical_chart epsilon hepsilon
  refine ⟨eta, delta₀, heta, hetaEpsilon, hd, hd1, ?_⟩
  intro delta hdelta hsmall F hn hb he hv hcwa Y hy hw f hf h0
  exact lower delta hdelta hsmall F hn hb he hv
    (dilatedTubeWolffVolumeBound_of_convexWolffBound hcwa) Y hy hw f hf h0

/-- Packing removes the cardinality premise under ordinary paper
distinctness; unit-ball containment supplies the base and height window. -/
theorem pure_wz2_dilated_tube_wolff_lower_bound_in_unit_ball :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∃ eta delta₀ : ℝ,
        0 < eta ∧ eta ≤ epsilon ∧ 0 < delta₀ ∧ delta₀ < 1 ∧
        ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
          ∀ F : Kakeya.Streamlined.TubeFamily delta,
            F.Nonempty → F.IsInUnitBall →
            WZ2PaperOrdinaryIsEssentiallyDistinct F → IsInVerticalChart F →
            DilatedTubeWolffVolumeBound F 32 (Kakeya.realRpowENN delta (-eta)) →
            ∀ Y : Kakeya.Streamlined.TubeShading F,
              Y.IsLambdaDense (Kakeya.realRpowENN delta eta) →
              ∀ f : SlopeFunction, f.IsNonsingular → f 0 = 0 →
                Kakeya.realRpowENN delta epsilon ≤
                  MeasureTheory.volume (twistedUnion Y f) := by
  intro epsilon hepsilon
  obtain ⟨eta, scale, heta, hetaEpsilon, _hetaOne, hscale, hscaleOne, hmain⟩ :=
    pure_wz2_proposition7_1_dilated_tube_wolff 7 (by norm_num) epsilon hepsilon
  obtain ⟨packingScale, hpackingScale, _hpackingOne, hpacking⟩ :=
    exists_delta_mul_rpow_le_rpow ((195 : ℝ) ^ 3 * 67 ^ 3) (by positivity)
      (show (-7 : ℝ) < -6 by norm_num)
  let delta₀ := min scale packingScale
  refine ⟨eta, delta₀, heta, hetaEpsilon, lt_min hscale hpackingScale,
    (min_le_left _ _).trans_lt hscaleOne, ?_⟩
  intro delta hdelta hdeltaLe F hnonempty hball hdistinct hvertical hwolff
    Y hdense f hnonsingular hzero
  have hdeltaScale : delta ≤ scale := hdeltaLe.trans (min_le_left _ _)
  have hdeltaOne : delta ≤ 1 := (hdeltaScale.trans_lt hscaleOne).le
  have hdeltaPacking : delta ≤ packingScale := hdeltaLe.trans (min_le_right _ _)
  have hbaseOne : HasBoundedBase F 1 := hasBoundedBase_of_isInUnitBall hdelta.le hball
  have hbase : HasBoundedBase F 4 := fun i => (hbaseOne i).trans (by norm_num)
  have hcardReal : (F.card : ℝ) ≤ Real.rpow delta (-7) :=
    (PureWZ2.wz2_ed_packing_bound hdelta hdeltaOne hdistinct
      (fun i => (hbaseOne i).trans (by norm_num))).trans
        (hpacking delta hdelta hdeltaPacking)
  have hcard : F.enncard ≤ Kakeya.realRpowENN delta (-7) := by
    simpa [Kakeya.Streamlined.TubeFamily.enncard, Kakeya.realRpowENN] using
      ENNReal.ofReal_le_ofReal hcardReal
  exact hmain delta hdelta hdeltaScale F hnonempty hbase hvertical
    hcard hwolff Y hdense
    (isInSlopeWindow_of_isInUnitBall hball Y) f hnonsingular hzero

/-- The unit-ball CWA endpoint uses the corrected finite coarse tests while
retaining every supplied fine unit segment at its original position. -/
theorem pure_wz2_convex_wolff_lower_bound_in_unit_ball_via_dilated_tubes :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∃ eta delta₀ : ℝ,
        0 < eta ∧ eta ≤ epsilon ∧ 0 < delta₀ ∧ delta₀ < 1 ∧
        ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
          ∀ F : Kakeya.Streamlined.TubeFamily delta,
            F.Nonempty → F.IsInUnitBall →
            WZ2PaperOrdinaryIsEssentiallyDistinct F → IsInVerticalChart F →
            WZ2PaperBodyConvexWolffBound F.toBodyFamily
              (Kakeya.realRpowENN delta (-eta)) →
            ∀ Y : Kakeya.Streamlined.TubeShading F,
              Y.IsLambdaDense (Kakeya.realRpowENN delta eta) →
              ∀ f : SlopeFunction, f.IsNonsingular → f 0 = 0 →
                Kakeya.realRpowENN delta epsilon ≤
                  MeasureTheory.volume (twistedUnion Y f) := by
  intro epsilon hepsilon
  obtain ⟨eta, delta₀, heta, hetaEpsilon, hd, hd1, lower⟩ :=
    pure_wz2_dilated_tube_wolff_lower_bound_in_unit_ball epsilon hepsilon
  refine ⟨eta, delta₀, heta, hetaEpsilon, hd, hd1, ?_⟩
  intro delta hdelta hsmall F hn hb he hv hcwa Y hy f hf h0
  exact lower delta hdelta hsmall F hn hb he hv
    (dilatedTubeWolffVolumeBound_of_bodyConvexWolffBound hcwa) Y hy f hf h0

end Kakeya.Assouad
