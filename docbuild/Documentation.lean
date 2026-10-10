import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
import MyLeanRepo.DiscretisedFurstenbergEstimate.BasicUniformization
import MyLeanRepo.DiscretisedFurstenbergEstimate.Contracts.Prop73
import MyLeanRepo.DiscretisedFurstenbergEstimate.Contracts.Theorem61
import MyLeanRepo.DiscretisedFurstenbergEstimate.FinalProof
import MyLeanRepo.DiscretisedFurstenbergEstimate.QuantitativeThickTubeCover
import MyLeanRepo.DiscretisedFurstenbergEstimate.RegularIncidence.Definitions
import MyLeanRepo.DiscretizedBSG
import MyLeanRepo.DiscretizedPluennecke
import MyLeanRepo.DiscretizedPluenneckeFull
import MyLeanRepo.Energy.EnergyToLargeMassDeltaSet
import MyLeanRepo.ExpansionLemma
import MyLeanRepo.ExpansionTheoremRecursive
import MyLeanRepo.Kakeya.AssertionD
import MyLeanRepo.Kakeya.Assouad.Definitions
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12Extremal
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05V4RichFinalAssembly
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Core
import MyLeanRepo.Kakeya.Assouad.PureWZ2.DirectWolffFloor
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.MultiScaleLocalAD
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope
import MyLeanRepo.Kakeya.Assouad.PureWZ2.ParameterFrostmanLowerBound
import MyLeanRepo.Kakeya.Assouad.PureWZ2.PropSticky
import MyLeanRepo.Kakeya.Assouad.PureWZ2.PropStickyReentry
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Theorem5_2Unconditional
import MyLeanRepo.Kakeya.Assouad.PureWZ2.TwistedProjection
import MyLeanRepo.Kakeya.Assouad.Statements
import MyLeanRepo.Kakeya.Assouad.Targets.ParameterBlockAmplification
import MyLeanRepo.Kakeya.Assouad.Targets.PureWZ2Node02CriticalExtraction
import MyLeanRepo.Kakeya.Assouad.Targets.PureWZ2Node03PropSticky
import MyLeanRepo.Kakeya.Assouad.Targets.PureWZ2Node04Grains
import MyLeanRepo.Kakeya.Assouad.Targets.PureWZ2Node06LargeSlope
import MyLeanRepo.Kakeya.Assouad.Targets.PureWZ2Node07SmallTwistedProjection
import MyLeanRepo.Kakeya.Assouad.Targets.ScaleProfileCrossing
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.FrostmanToKatzTao
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ParameterBlockAmplificationStatement
import MyLeanRepo.Kakeya.Assouad.WZ1.AnisotropicFrostmanRescaling
import MyLeanRepo.Kakeya.Assouad.WZ1.Corollary26Statements
import MyLeanRepo.Kakeya.Assouad.WZ1.Definitions
import MyLeanRepo.Kakeya.Assouad.WZ1.DiscreteThinTubes
import MyLeanRepo.Kakeya.Assouad.WZ1.FrostmanCoarsening
import MyLeanRepo.Kakeya.Assouad.WZ1.FrostmanEnergy
import MyLeanRepo.Kakeya.Assouad.WZ1.HypergraphRefinement
import MyLeanRepo.Kakeya.Assouad.WZ1.KaufmanProjection
import MyLeanRepo.Kakeya.Assouad.WZ1.LineNonconcentrationProjection
import MyLeanRepo.Kakeya.Assouad.WZ1.MainChainStatements
import MyLeanRepo.Kakeya.Assouad.WZ1.ProjectionTheoremFinalStatements
import MyLeanRepo.Kakeya.Assouad.WZ1.ProjectionTheoremFirstLayerStatements
import MyLeanRepo.Kakeya.Assouad.WZ1.ProjectionTheoremLocalizationStatements
import MyLeanRepo.Kakeya.Assouad.WZ1.QuarterThinTubes
import MyLeanRepo.Kakeya.Assouad.WZ1.SmoothSegmentExtension
import MyLeanRepo.Kakeya.Assouad.WZ1.SmoothedToDiscreteThinTubesStatement
import MyLeanRepo.Kakeya.Assouad.WZ1.Statements
import MyLeanRepo.Kakeya.Assouad.WZ1.ThinTubesLargeDotProduct
import MyLeanRepo.Kakeya.Assouad.WZ1.TwoEndsReduction
import MyLeanRepo.Kakeya.Assouad.WZ1.WellSeparatedProjectionUnion
import MyLeanRepo.Kakeya.CV.MultilinearKakeya
import MyLeanRepo.Kakeya.CV.MultilinearKakeya.Complete
import MyLeanRepo.Kakeya.CV.PolynomialBadSetCover
import MyLeanRepo.Kakeya.CV.PolynomialVisibilityComplete
import MyLeanRepo.Kakeya.CV.StableEllipsoidColouring
import MyLeanRepo.Kakeya.CV.Statements
import MyLeanRepo.Kakeya.CV.Targets.EllipsoidSelectionStability
import MyLeanRepo.Kakeya.CV.Targets.PolynomialCylinderEstimate
import MyLeanRepo.Kakeya.CV.Targets.PreliminaryReduction
import MyLeanRepo.Kakeya.CV.Targets.VisibilityDegreeBound
import MyLeanRepo.Kakeya.CV.Targets.VisibilityDirectionalBound
import MyLeanRepo.Kakeya.Cinematic.BipartiteTangencyReduction.PerPair
import MyLeanRepo.Kakeya.Cinematic.Definitions
import MyLeanRepo.Kakeya.Cinematic.Geometry
import MyLeanRepo.Kakeya.Cinematic.Section5.UniformC2ConcreteAssembly
import MyLeanRepo.Kakeya.Cinematic.Statements
import MyLeanRepo.Kakeya.Cinematic.Targets.BipartiteTangencyRobustFull
import MyLeanRepo.Kakeya.Cinematic.Targets.CommonTangentRectangleRobust
import MyLeanRepo.Kakeya.Cinematic.Targets.ComparableRectangles
import MyLeanRepo.Kakeya.Cinematic.Targets.MarcusTardosGraphLenses
import MyLeanRepo.Kakeya.Cinematic.Targets.MaximalFineRectangleSelection
import MyLeanRepo.Kakeya.Cinematic.Targets.RectanglePacking
import MyLeanRepo.Kakeya.Cinematic.Targets.TangencySublevelDiameter
import MyLeanRepo.Kakeya.Cinematic.Targets.TwoZeros
import MyLeanRepo.Kakeya.Cinematic.WZ2UniformC2Input
import MyLeanRepo.Kakeya.Streamlined.Families
import MyLeanRepo.Lemma51Corollary
import MyLeanRepo.MarstrandArbitraryDim
import MyLeanRepo.OSW.RuzsaCorollaries
import MyLeanRepo.RadialBootstrapping.HasMeasureThinTubes
import MyLeanRepo.RuzsaTriangle
import MyLeanRepo.StrongRingTheoremCorrected
import MyLeanRepo.SupportFreeFrostman
import MyLeanRepo.UniformExpansionLemma
import MyLeanRepo.WeakTwoEndsSumProduct
import MyLeanRepo.discretised_furstenberg_estimate
import MyLeanRepo.radial_bootstrapping_measure_thin_tubes

/-!
# The sticky Kakeya theorem in Lean

The [mathematical blueprint](../blueprint/index.html) follows the argument
through Wang and Zahl's finite sticky estimate. This documentation contains
the declarations linked from that account and their full dependency chain.

The closed proof is `Kakeya.Assouad.PureWZ2Theorem5_2Unconditional`.
Its type is the following proposition, defined in
`Kakeya.Assouad.PureWZ2Theorem5_2Statement`:

```lean
def PureWZ2Theorem5_2Statement : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon →
    ∃ eta delta₀ : ℝ,
      0 < eta ∧
      0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
        ∀ family : Kakeya.Streamlined.TubeFamily delta,
          family.Nonempty →
          WZ2PaperPureCWAAtNearbyScales family
            (Kakeya.realRpowENN delta (-eta)) →
          ∀ shading : Kakeya.Streamlined.TubeShading family,
            shading.IsLambdaDense
              (Kakeya.realRpowENN delta eta) →
            Kakeya.realRpowENN delta epsilon ≤
              volume shading.union
```

Long definitions may be abbreviated in doc-gen4's Equations sections.
Each declaration's source button opens its full definition or proof.

The imports of this module match `blueprint/lean-imports.txt`. The build checks
both that list and the displayed statement against their source files.
-/
