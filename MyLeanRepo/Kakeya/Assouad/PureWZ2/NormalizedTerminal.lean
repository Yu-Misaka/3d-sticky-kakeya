import MyLeanRepo.Kakeya.Assouad.PureWZ2.TwistedProjection

/-!
# One configuration for the upper bound and the CWA lower bound

The old preparation record remains unchanged.  Its strengthened replacement
retains Convex Wolff on the very same ordinary family.  The refinement record
also retains the actual index map and shading containment from cleanup.
-/

noncomputable section
namespace Kakeya.Assouad

/-- A normalized Lemma 6.7 configuration on which the independent CWA
projection lower bound can be evaluated directly. -/
structure PureWZ2NormalizedProjectionData (sigma loss delta : ℝ)
    extends PureWZ2ParameterFrostmanPreparationData sigma loss delta where
  convex_wolff : ConvexWolffBound family (Kakeya.realRpowENN delta (-loss))

/-- The terminal configuration is a literal subfamily and subshading of the
specified affine preparation.  In particular no second configuration can
supply its CWA certificate or projection upper bound. -/
structure PureWZ2NormalizedProjectionRefinement
    {delta : ℝ} (ambient : Kakeya.Streamlined.TubeFamily delta)
    (ambientShading : Kakeya.Streamlined.TubeShading ambient)
    (slope : SlopeFunction) (sigma loss : ℝ) where
  configuration : PureWZ2NormalizedProjectionData sigma loss delta
  sourceIndex : Fin configuration.family.card → Fin ambient.card
  sourceIndex_injective : Function.Injective sourceIndex
  tube_eq_source : ∀ i, configuration.family.tube i = ambient.tube (sourceIndex i)
  shading_subset_source : ∀ i,
    configuration.shading.carrier i ⊆ ambientShading.carrier (sourceIndex i)
  slope_eq : configuration.analysisSlope = slope.centered

/-- All loss and scale choices precede the single terminal configuration. -/
def PureWZ2NormalizedProjectionStatement : Prop :=
  ∀ sigma : ℝ, PureWZ2CriticalPackage sigma →
    ∀ loss scaleCeiling : ℝ, 0 < loss → loss < sigma → 0 < scaleCeiling →
      ∃ delta : ℝ, 0 < delta ∧ delta ≤ scaleCeiling ∧ delta < 1 ∧
        Nonempty (PureWZ2NormalizedProjectionData sigma loss delta)

/-- Preserve the historical preparation API by forgetting only the extra
CWA certificate, without making another existential choice. -/
theorem PureWZ2NormalizedProjectionStatement.toPreparation
    (h : PureWZ2NormalizedProjectionStatement) :
    PureWZ2ParameterFrostmanPreparationStatement := by
  intro sigma critical loss scaleCeiling hloss hsig hscale
  obtain ⟨delta, hd, hdc, hd1, ⟨data⟩⟩ :=
    h sigma critical loss scaleCeiling hloss hsig hscale
  exact ⟨delta, hd, hdc, hd1, ⟨data.toPureWZ2ParameterFrostmanPreparationData⟩⟩

end Kakeya.Assouad
end
