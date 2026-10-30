import MyLeanRepo.Kakeya.Assouad.PureWZ2.FullLineTubeWolffLowerBound
import MyLeanRepo.Kakeya.Assouad.PureWZ2.ParameterFrostmanLowerBound
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Section7Nonconcentration
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.WZ2EDSeparation
import MyLeanRepo.Kakeya.Assouad.ProjectionNormalization
import MyLeanRepo.Kakeya.Assouad.ConstantAbsorption

/-!
# The normalized CWA lower bound with the paper's ordinary distinctness

This variant uses the literal ordinary centered-dilation distinctness and
unnormalized indexed CWA count.  Both the polynomial cardinality budget and
the parameter Frostman condition are derived.  Unit-ball containment supplies
the base and shading-window bounds.  The vertical chart and f(0)=0 remain
explicit: no claim of the generic paper Proposition 6.8 is made.
-/

namespace Kakeya.Assouad

/-- The unit-ball CWA lower bound in a normalized vertical chart, with WZ2's
ordinary distinctness convention.  No analytic half-overlap distinctness,
parameter-count, or cardinality upper-bound hypothesis is required. -/
theorem pure_wz2_convex_wolff_lower_bound_in_unit_ball :
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
  obtain ⟨sourceEta, scale, heta, hetaEpsilon, _hetaOne, hscale, hscaleOne, hmain⟩ :=
    pure_wz2_proposition7_1_full_line_tube_wolff 7 (by norm_num) epsilon hepsilon
  obtain ⟨packingScale, hpackingScale, _hpackingOne, hpacking⟩ :=
    exists_delta_mul_rpow_le_rpow ((195 : ℝ) ^ 3 * 67 ^ 3) (by positivity)
      (show (-7 : ℝ) < -6 by norm_num)
  let eta := sourceEta
  let delta₀ := min scale packingScale
  have heta' : 0 < eta := by dsimp [eta]; linarith
  have hetaEpsilon' : eta ≤ epsilon := by dsimp [eta]; linarith
  refine ⟨eta, delta₀, heta', hetaEpsilon', by positivity,
    (min_le_left _ _).trans_lt hscaleOne, ?_⟩
  intro delta hdelta hdeltaLe F hnonempty hball hdistinct hvertical hcwa
    Y hdense f hnonsingular hzero
  have hdeltaScale : delta ≤ scale := hdeltaLe.trans (min_le_left _ _)
  have hdeltaOne : delta ≤ 1 := (hdeltaScale.trans_lt hscaleOne).le
  have hdeltaPacking : delta ≤ packingScale :=
    hdeltaLe.trans (min_le_right _ _)
  have hbaseOne : HasBoundedBase F 1 := hasBoundedBase_of_isInUnitBall hdelta.le hball
  have hbase : HasBoundedBase F 4 := fun i => (hbaseOne i).trans (by norm_num)
  have hcardReal : (F.card : ℝ) ≤ Real.rpow delta (-7) :=
    (PureWZ2.wz2_ed_packing_bound hdelta hdeltaOne hdistinct
      (fun i => (hbaseOne i).trans (by norm_num))).trans
        (hpacking delta hdelta hdeltaPacking)
  have hcard : F.enncard ≤ Kakeya.realRpowENN delta (-7) := by
    simpa [Kakeya.Streamlined.TubeFamily.enncard, Kakeya.realRpowENN] using
      ENNReal.ofReal_le_ofReal hcardReal
  have hwolff : FullLineTubeWolffBound F 6 (Kakeya.realRpowENN delta (-sourceEta)) :=
    fullLineTubeWolffBound_of_bodyConvexWolffBound hcwa
  exact hmain delta hdelta hdeltaScale F hnonempty hbase hvertical
    hcard hwolff Y hdense
    (isInSlopeWindow_of_isInUnitBall hball Y) f hnonsingular hzero

end Kakeya.Assouad
