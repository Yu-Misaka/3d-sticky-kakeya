import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.GridOSBoundedOneScaleFromBlock
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.SignedWindowSharpDensity
import MyLeanRepo.Kakeya.Assouad.Targets.ScaleProfileCrossing
import MyLeanRepo.Kakeya.Assouad.Targets.TubeParameterClusterFrostman
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ParameterWindowClusterCardinality
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ParameterLocalSpacingCandidateFromInterval
import MyLeanRepo.Kakeya.Assouad.Targets.ParameterSpacingIntervalCertificate
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ParameterLocalFrostmanBlockPruning
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ParameterLocalFullBlockFromSpacing
import MyLeanRepo.Kakeya.Assouad.Targets.ParameterBlockAmplification
import MyLeanRepo.Kakeya.Assouad.Targets.HalfParameterCinematicPYZGeneral
import MyLeanRepo.Kakeya.Assouad.Targets.CompactSubshadingSelection
import MyLeanRepo.Kakeya.Assouad.Targets.CompactTubeTwistedProjectionArea
import MyLeanRepo.Kakeya.Assouad.Targets.AssignedCurveProjectionContainment
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ParameterBlockRepresentativeCinematicPullback
import MyLeanRepo.Kakeya.Assouad.Targets.ParameterBlockProjectionUniformizationFromOS
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ParameterBlockProjectionArithmetic
import MyLeanRepo.Kakeya.Assouad.Targets.PerTubeMassPruning
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ProjectedFiberOSPreparation
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ProjectedFiberOSLevelCellSystem
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ParameterLocalBlockProjectionCorridor
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ProjectedFiberOSCinematicGlobalization
import MyLeanRepo.Kakeya.Assouad.Targets.ParameterBlockPositiveWindowAssembly

/-!
# WZ2 Lemma 7.12: the complete parameter-Frostman one-step estimate

This closes the curve construction/jet count, replicated projected mass,
PYZ (WZ2 Theorem 7.13), Holder, projection uniformization, positive-window
assembly and reflection in a single callable theorem.  Projection
uniformization is a predecessor, not the whole one-step theorem.

The result returns a same-family subshading, its density, the growing target
radius and the comparison with its own coarse target neighbourhood.  It is
the normalized parameter-Frostman version, not the carrier Tube-Wolff-only
paper statement.  In particular, no cardinality upper bound or essential
distinctness is imposed by this step.
-/

namespace Kakeya.Assouad

/-- Closed normalized WZ2 Lemma 7.12 with the density exponents η → 4η.
The improved OS retention pays for the signed-window selection. -/
theorem pure_wz2_lemma7_12_parameter_frostman_sharp_density :
    GridOSBoundedOneScaleSharpInput := by
  have hScaleProfile : ScaleProfileCrossingStatement :=
    scale_profile_crossing
  have hParameterCluster : TubeParameterClusterFrostmanStatement :=
    tube_parameter_cluster_frostman
  have hWindowCluster : ParameterWindowClusterCardinalityStatement :=
    parameter_window_cluster_cardinality
  have hSpacing : ParameterLocalSpacingCandidateStatement :=
    parameter_local_spacing_candidate_from_interval
      parameter_spacing_interval_certificate
  have hLocalBlock : ParameterLocalFullBlockSelectionStatement :=
    parameter_local_full_block_from_spacing
      hSpacing parameter_local_frostman_block_pruning
  have hAmplification : ParameterBlockAmplificationStatement :=
    parameter_block_amplification
  have hHalfPYZ : HalfParameterCinematicPYZGeneralStatement :=
    half_parameter_cinematic_pyz_general
  have hCompactSelection : CompactSubshadingSelectionStatement :=
    compact_subshading_selection
  have hCompactArea : CompactTubeTwistedProjectionAreaStatement :=
    compact_tube_twisted_projection_area
  have hContainment :
      AssignedCurveProjectionContainmentFromVerticalChartStatement :=
    assigned_curve_projection_containment_from_vertical_chart
  have hPullback :
      ParameterBlockRepresentativeCinematicPullbackStatement :=
    parameter_block_representative_cinematic_pullback
  have hUniformity :
      ParameterBlockProjectionUniformizationWithDensityStatement 3 :=
    parameter_block_projection_uniformization_from_os_with_density 3
      parameter_block_projection_arithmetic
      per_tube_mass_pruning
      projected_fiber_os_preparation_with_density
      projected_fiber_os_level_cell_system
      parameter_local_block_projection_corridor
      projected_fiber_os_cinematic_globalization
  have hAssembly : ParameterBlockPositiveWindowAssemblyWithDensityStatement 3 :=
    parameter_block_positive_window_assembly_with_density 3
  have hPositive := hAssembly
    hScaleProfile hParameterCluster hWindowCluster hLocalBlock
    hAmplification hHalfPYZ hCompactSelection hCompactArea
    hContainment hPullback hUniformity
  exact grid_os_bounded_one_scale_sharp_from_positive hPositive
    compact_assigned_cinematic_holder_from_vertical_chart pyz_input

/-- The original η/2 → 4η API is a specialization of the sharper theorem.
The finite GridOS iteration and its quantifier order remain compatible. -/
theorem pure_wz2_lemma7_12_parameter_frostman :
    GridOSBoundedOneScaleInput :=
  pure_wz2_lemma7_12_parameter_frostman_sharp_density.toLegacy

end Kakeya.Assouad
