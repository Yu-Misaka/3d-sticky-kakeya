import MyLeanRepo.Kakeya.Assouad.PureWZ2.ParameterFrostmanLowerBound
import MyLeanRepo.Kakeya.Assouad.PureWZ2.FullLineTubeWolff
import MyLeanRepo.Kakeya.Assouad.ConstantAbsorption

/-!
# Projection lower bound from physical full-line Tube Wolff tests

The only nonconcentration premise is the count in full-line tubes clipped
to the fixed ball.  The geometric lemma derives parameter Frostman before
the existing one-step/GridOS/telescoping engine is invoked.  The polynomial
cardinality exponent, chart and slope normalization remain explicit.
-/

namespace Kakeya.Assouad

/-- A normalized Tube-Wolff-only Proposition 7.1 for full-line coarse tests.
The fixed polynomial cardinality budget precedes epsilon and the cutoff. -/
theorem pure_wz2_proposition7_1_full_line_tube_wolff
    (cardExponent : ℝ) (hcardExponent : 0 < cardExponent) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∃ eta delta₀ : ℝ,
        0 < eta ∧ eta ≤ epsilon ∧ eta ≤ 1 ∧ 0 < delta₀ ∧ delta₀ < 1 ∧
        ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
          ∀ F : Kakeya.Streamlined.TubeFamily delta,
            F.Nonempty → HasBoundedBase F 4 → IsInVerticalChart F →
            F.enncard ≤ Kakeya.realRpowENN delta (-cardExponent) →
            FullLineTubeWolffBound F 6 (Kakeya.realRpowENN delta (-eta)) →
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
    exists_delta_mul_rpow_le_rpow 172800 (by norm_num)
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
  have hconstant : 172800 * Kakeya.realRpowENN delta (-eta) ≤
      Kakeya.realRpowENN delta (-sourceEta) := by
    have h := ENNReal.ofReal_le_ofReal (habsorb delta hdelta hdeltaAbsorb)
    simpa [eta, Kakeya.realRpowENN,
      ENNReal.ofReal_mul (show (0 : ℝ) ≤ 172800 by norm_num)] using h
  have hfrostman : TubeParameterFrostmanBound F
      (Kakeya.realRpowENN delta (-sourceEta)) := by
    intro r hdeltaR hrOne reference
    exact (tubeParameterFrostmanBound_of_fullLineTubeWolffBound hdelta
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

end Kakeya.Assouad
