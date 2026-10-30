import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.GridOSFiniteRunStatements
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.GridOSFinalConstantAbsorptionStatement
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.GridOSReadyStateStatements
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.GridOSTerminalClosureStatement
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.GridOSTerminationStatement
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.TubeParameterGridOSInitialStateStatements

/-!
# Final corrected parameter-Frostman Section 7 estimate

This is the direct finite-iteration boundary used by WZ2 Theorem 5.2.
Every input is callable: no conditional theorem is nested without the leaves
needed to instantiate it.

The route proves the explicit indexed parameter-Frostman specialization
actually supplied by WZ Lemma 8.  It does not assert the legacy
TubeWolff-only implication for freely translated unit segments.
-/

namespace Kakeya.Assouad

/--
Assemble the final parameter-Frostman twisted-projection lower bound from the
corrected terminal-grid initial state, finite scheduled iteration, and
terminal arithmetic.
-/
def GridOSParameterFrostmanEstimateStatement : Prop :=
  GridOSBoundedOneScaleInput →
    TubeParameterGridOSInitialStateInput →
      GridOSEffectiveLossScheduleStatement →
        GridOSInitialReadyStateInput →
          GridOSStateDichotomyInput →
            GridOSTransitionReadyStateStatement →
              GridOSFiniteStepScheduleInput →
                GridOSFiniteRunStatement →
                  GridOSTerminationStatement →
                    GridOSTerminalClosureInput →
                      GridOSFinalConstantAbsorptionStatement →
                        TwistedProjectionParameterFrostmanEstimateStatement

/-- Parameter-Frostman lower bound with only the data consumed by the finite
iteration.  A fixed polynomial budget replaces the extremal cardinality
window.  No carrier Tube-Wolff or essential-distinctness premise is needed. -/
def TwistedProjectionParameterFrostmanPolynomialEstimateStatement
    (cardExponent : ℝ) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon →
    ∃ eta delta₀ : ℝ,
      0 < eta ∧ eta ≤ epsilon ∧ eta ≤ 1 ∧
      0 < delta₀ ∧ delta₀ < 1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
        ∀ F : Kakeya.Streamlined.TubeFamily delta,
          F.Nonempty → IsInVerticalChart F →
          (∀ i : Fin F.card,
            |(tubeParams i).a| ≤ 12 ∧ |(tubeParams i).b| ≤ 12 ∧
            |(tubeParams i).c| ≤ 2 ∧ |(tubeParams i).d| ≤ 2) →
          F.enncard ≤ Kakeya.realRpowENN delta (-cardExponent) →
          TubeParameterFrostmanBound F (Kakeya.realRpowENN delta (-eta)) →
          ∀ Y : Kakeya.Streamlined.TubeShading F,
            Y.IsLambdaDense (Kakeya.realRpowENN delta eta) →
            IsInSlopeWindow Y →
            ∀ f : SlopeFunction, f.IsNonsingular → f 0 = 0 →
              Kakeya.realRpowENN delta epsilon ≤
                MeasureTheory.volume (twistedUnion Y f)

/-- The finite GridOS engine for a fixed polynomial cardinality budget. -/
def GridOSParameterFrostmanPolynomialEstimateStatement
    (cardExponent : ℝ) : Prop :=
  GridOSBoundedOneScaleInput →
    TubeParameterGridOSInitialStatePolynomialInput cardExponent →
      GridOSEffectiveLossScheduleStatement →
        GridOSInitialReadyStateInput →
          GridOSStateDichotomyInput →
            GridOSTransitionReadyStateStatement →
              GridOSFiniteStepScheduleInput →
                GridOSFiniteRunStatement →
                  GridOSTerminationStatement →
                    GridOSTerminalClosureInput →
                      GridOSFinalConstantAbsorptionStatement →
                        TwistedProjectionParameterFrostmanPolynomialEstimateStatement cardExponent

end Kakeya.Assouad
