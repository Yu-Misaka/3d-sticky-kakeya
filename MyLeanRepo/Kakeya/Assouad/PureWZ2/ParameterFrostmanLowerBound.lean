import MyLeanRepo.Kakeya.Assouad.PureWZ2.ProjectionOneStep
import MyLeanRepo.Kakeya.Assouad.Targets.TwistedProjectionParameterFrostmanEstimate

/-!
# Pure WZ2 parameter-Frostman lower bounds

The finite iteration now calls the complete closed Lemma 7.12.  Any fixed
polynomial cardinality budget is allowed; the legacy extremal-cardinality
interface is preserved below.  A carrier Tube-Wolff-to-parameter reduction
is not presumed.
-/

namespace Kakeya.Assouad

/-- Closed normalized Proposition 7.1 with a fixed polynomial cardinality
budget, chosen before the output loss and small-scale threshold. -/
theorem pure_wz2_proposition7_1_parameter_frostman
    (cardExponent : ℝ) (hcardExponent : 0 < cardExponent) :
    TwistedProjectionParameterFrostmanPolynomialEstimateStatement cardExponent :=
  twisted_projection_parameter_frostman_polynomial_of_one_step
    cardExponent hcardExponent pure_wz2_lemma7_12_parameter_frostman

/-- Compatibility with the original Section 7 parameter-Frostman contract. -/
theorem pure_wz2_twisted_projection_parameter_frostman_lower_bound :
    TwistedProjectionParameterFrostmanEstimateStatement :=
  twisted_projection_parameter_frostman_of_polynomial
    (pure_wz2_proposition7_1_parameter_frostman 3 (by norm_num))

end Kakeya.Assouad
