import MyLeanRepo.Kakeya.Assouad.PureWZ2.Theorem5_2Unconditional
import MyLeanRepo.Kakeya.Assouad.PureWZ2.PaperNormalizedProjectionLowerBound
import MyLeanRepo.Kakeya.Assouad.PureWZ2.SlopeOffsetCounterexample
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LongitudinalTubeWolffObstruction
import MyLeanRepo.Kakeya.Assouad.PureWZ2.DilatedTubeWolffLowerBound
import MyLeanRepo.Kakeya.Assouad.PureWZ2.OrdinaryTubeWolff
import Lean

/-! Executable interface, axiom, and upstream-argument audit for the Core DAG. -/

namespace Kakeya.Assouad

-- The historical public contracts, including the unconditional final entry.
example : PureWZ2PropStickyStatement := pure_wz2_node03_prop_sticky
example : PureWZ2GrainsStatement := pure_wz2_node04_grains
example : PureWZ2C2GrainsStatement := pure_wz2_node05_c2_grains
example : PureWZ2LargeSlopeStatement := pure_wz2_node06_large_slope
example : PureWZ2SmallTwistedProjectionStatement := pure_wz2_node07_small_twisted_projection
example : PureWZ2Theorem5_2AssemblyStatement := pure_wz2_node08_theorem5_2
example : PureWZ2Theorem5_2Statement := PureWZ2Theorem5_2Unconditional
example : PureWZ2Theorem5_2Statement := pure_wz2_theorem5_2_unconditional
example : TwistedProjectionParameterFrostmanEstimateStatement :=
  pure_wz2_twisted_projection_parameter_frostman_lower_bound
example : GridOSBoundedOneScaleInput := pure_wz2_lemma7_12_parameter_frostman
example : GridOSBoundedOneScaleSharpInput :=
  pure_wz2_lemma7_12_parameter_frostman_sharp_density
example : PureWZ2NormalizedProjectionStatement := pure_wz2_left_line_normalized_projection
example : PureWZ2CommonHeightProjectionStatement := pure_wz2_left_line_common_height_projection
example : PureWZ2C2PrescribedIntervalsStatement :=
  pure_wz2_left_line_c2_prescribed_intervals
example : ¬ PureWZ2UnrestrictedTubeWolffProjectionStatement :=
  not_pureWZ2UnrestrictedTubeWolffProjectionStatement
example : ¬ PureWZ2NormalizedOrdinaryTubeWolffProjectionStatement :=
  not_pureWZ2NormalizedOrdinaryTubeWolffProjectionStatement

-- Factor one is exactly the historical ordinary-volume predicate.
example {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta} {C : ENNReal} :
    DilatedTubeWolffVolumeBound F 1 C ↔ OrdinaryTubeWolffVolumeBound F C :=
  dilatedTubeWolffVolumeBound_one_iff

-- The CWA certificate is indexed by the same family as the upper bound.
example {sigma loss delta : ℝ} (d : PureWZ2NormalizedProjectionData sigma loss delta) :
    ConvexWolffBound d.toPureWZ2ParameterFrostmanPreparationData.family
      (Kakeya.realRpowENN delta (-loss)) := d.convex_wolff

-- The corrected coarse tests use exactly that family and the same loss.
example {sigma loss delta : ℝ} (d : PureWZ2NormalizedProjectionData sigma loss delta) :
    DilatedTubeWolffVolumeBound d.family 32
      (Kakeya.realRpowENN delta (-loss)) :=
  dilatedTubeWolffVolumeBound_of_convexWolffBound d.convex_wolff

-- The refinement carries actual tube and shading transport, not just an origin label.
example {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F} {f : SlopeFunction} {sigma loss : ℝ}
    (d : PureWZ2NormalizedProjectionRefinement F Y f sigma loss) :
    d.configuration.shading.union ⊆ Y.union := by
  rintro p ⟨i, hi⟩
  exact ⟨d.sourceIndex i, d.shading_subset_source i hi⟩

-- The actual paper terminal is transported, with every source index retained.
example {delta sigma loss : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : WZ1PaperTubeShading F} {f : SlopeFunction}
    (d : PureWZ2PaperTerminalProjectionRefinement F Y f sigma loss) :
    HasCommonHeightTubeModel d.configuration.family := d.common_height

example {delta sigma loss : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : WZ1PaperTubeShading F} {f : SlopeFunction}
    (d : PureWZ2PaperTerminalProjectionRefinement F Y f sigma loss) :
    d.configuration.shading.union ⊆ slopeOffsetLinear (f 0) '' Y.union := by
  rintro p ⟨i, hi⟩
  obtain ⟨q, hq, rfl⟩ := d.shading_subset_image i hi
  exact ⟨q, ⟨d.sourceIndex i, hq.1⟩, rfl⟩

example {delta sigma loss : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : WZ1PaperTubeShading F} {f : SlopeFunction}
    (d : PureWZ2PaperTerminalProjectionRefinement F Y f sigma loss) :
    MeasureTheory.volume (twistedUnion d.configuration.shading d.configuration.analysisSlope) ≤
      ENNReal.ofReal (slopeOffsetScale (f 0)) *
        MeasureTheory.volume (twistedProjection f '' Y.union) :=
  d.projection_volume_le

end Kakeya.Assouad

open Lean Elab Command Meta

run_cmd do
  let names := #[
    `Kakeya.Assouad.pure_wz2_node03_rich_prop62_kernel,
    `Kakeya.Assouad.pure_wz2_node04_reentrant_grains,
    `Kakeya.Assouad.pure_wz2_left_line_c2_grains,
    `Kakeya.Assouad.pureWZ2ShortGlobalGrain_subset_segment,
    `Kakeya.Assouad.pureWZ2ShortGlobalGrain_dist,
    `Kakeya.Assouad.pureWZ2_frameProjectedNormal_lower_of_long_axis,
    `Kakeya.Assouad.pureWZ2_dense_short_global_grain_normal,
    `Kakeya.Assouad.pureWZ2_dense_cell_label_refinement,
    `Kakeya.Assouad.pureWZ2_short_grain_label_count,
    `Kakeya.Assouad.pureWZ2_short_grain_packet_geometry,
    `Kakeya.Assouad.pureWZ2_prescribed_slab_frame_preparation,
    `Kakeya.Assouad.PureWZ2Lemma31SlabAssembly.derivative_lower,
    `Kakeya.Assouad.PureWZ2Lemma31ScaleAssembly.derivative_lower,
    `Kakeya.Assouad.pure_wz2_lemma66_prepared_interval_on,
    `Kakeya.Assouad.pure_wz2_lemma66_normalized_interval,
    `Kakeya.Assouad.pure_wz2_lemma66_prepared_interval,
    `Kakeya.Assouad.pure_wz2_lemma66_prepared,
    `Kakeya.Assouad.pureWZ2_c2_source_with_fine_cap,
    `Kakeya.Assouad.pureWZ2_interval_ready_c2_source,
    `Kakeya.Assouad.pureWZ2_c2_source_with_prescribed_intervals,
    `Kakeya.Assouad.pure_wz2_left_line_c2_prescribed_intervals,
    `Kakeya.Assouad.pure_wz2_lemma66_prescribed_interval,
    `Kakeya.Assouad.pureWZ2PrescribedSlabHull_mass,
    `Kakeya.Assouad.pureWZ2PrescribedSlabHull_witness,
    `Kakeya.Assouad.pureWZ2PrescribedSlabHull_cover,
    `Kakeya.Assouad.pureWZ2PrescribedSlabHull_multiplicity,
    `Kakeya.Assouad.pureWZ2PrescribedSlabHull_height,
    `Kakeya.Assouad.pure_wz2_left_line_large_slope_retained,
    `Kakeya.Assouad.deltaMax_to_normalized_convexWolff,
    `Kakeya.Assouad.pure_wz2_node7_analytic_cleanup_with_cwa,
    `Kakeya.Assouad.pure_wz2_node7b_normalized_from_retained_large_slope,
    `Kakeya.Assouad.pure_wz2_left_line_normalized_projection,
    `Kakeya.Assouad.pure_wz2_left_line_lemma67,
    `Kakeya.Assouad.slopeOffset_twisted_volume,
    `Kakeya.Assouad.slopeOffsetLinear_axis_image,
    `Kakeya.Assouad.slopeOffsetSlabShading_dense,
    `Kakeya.Assouad.slopeOffsetRetubedFamily_cwa,
    `Kakeya.Assouad.exists_actual_terminal_slope_offset_cutoff_for_output_loss,
    `Kakeya.Assouad.pure_wz2_paper_terminal_normalization_cutoff,
    `Kakeya.Assouad.PureWZ2PaperTerminalProjectionRefinement.projection_volume_le,
    `Kakeya.Assouad.projected_fiber_os_preparation_with_density,
    `Kakeya.Assouad.parameter_block_projection_uniformization_from_os_with_density,
    `Kakeya.Assouad.parameter_block_positive_window_assembly_with_density,
    `Kakeya.Assouad.grid_os_bounded_one_scale_sharp_from_positive,
    `Kakeya.Assouad.pure_wz2_lemma7_12_parameter_frostman_sharp_density,
    `Kakeya.Assouad.pure_wz2_lemma7_12_parameter_frostman,
    `Kakeya.Assouad.pure_wz2_proposition7_1_parameter_frostman,
    `Kakeya.Assouad.fullLineTubeWolffBound_of_convexWolffBound,
    `Kakeya.Assouad.tubeParameterFrostmanBound_of_fullLineTubeWolffBound,
    `Kakeya.Assouad.pure_wz2_proposition7_1_full_line_tube_wolff,
    `Kakeya.Assouad.pure_wz2_full_line_tube_wolff_lower_bound_in_vertical_chart,
    `Kakeya.Assouad.pure_wz2_convex_wolff_lower_bound_in_vertical_chart,
    `Kakeya.Assouad.pure_wz2_convex_wolff_lower_bound_in_unit_ball,
    `Kakeya.Assouad.commonHeight_axisPoint_dist,
    `Kakeya.Assouad.commonHeight_direction_dist,
    `Kakeya.Assouad.commonHeight_segment_point_dist,
    `Kakeya.Assouad.commonHeight_modelTube_carrier_subset,
    `Kakeya.Assouad.tubeParameterFrostmanBound_of_commonHeightTubeWolffBound,
    `Kakeya.Assouad.ordinaryTubeWolffVolumeBound_of_convexWolffBound,
    `Kakeya.Assouad.tubeParameterFrostmanBound_of_commonHeightOrdinaryTubeWolff,
    `Kakeya.Assouad.pure_wz2_proposition7_1_ordinary_tube_wolff,
    `Kakeya.Assouad.pure_wz2_ordinary_tube_wolff_lower_bound_in_common_height_chart,
    `Kakeya.Assouad.pure_wz2_convex_wolff_lower_bound_in_common_height_chart,
    `Kakeya.Assouad.pure_wz2_ordinary_tube_wolff_lower_bound_in_unit_ball,
    `Kakeya.Assouad.PureWZ2PaperTerminalProjectionRefinement.common_height,
    `Kakeya.Assouad.pure_wz2_node7b_common_height_from_retained_large_slope,
    `Kakeya.Assouad.pure_wz2_left_line_common_height_projection,
    `Kakeya.Assouad.pure_wz2_no_critical_package_of_common_height_projection,
    `Kakeya.Assouad.pure_wz2_theorem5_2_of_common_height_projection,
    `Kakeya.Assouad.ordinaryTube_volume_eq,
    `Kakeya.Assouad.ordinaryTube_not_subset_of_radius_lt,
    `Kakeya.Assouad.TubeWolffBound.to_ordinaryVolume,
    `Kakeya.Assouad.OrdinaryTubeWolffVolumeBound.to_radiusSquared,
    `Kakeya.Assouad.offsetObstruction_projection_volume_le,
    `Kakeya.Assouad.planarTubeGrid_parameter_frostman,
    `Kakeya.Assouad.tubeParameterFrostman_to_centered_tubeWolff,
    `Kakeya.Assouad.planarTubeGrid_ordinary_distinct,
    `Kakeya.Assouad.planarTubeGrid_in_unitBall,
    `Kakeya.Assouad.exists_ordinary_tubeWolff_slope_offset_counterexample,
    `Kakeya.Assouad.not_pureWZ2UnrestrictedTubeWolffProjectionStatement,
    `Kakeya.Assouad.ordinary_capsule_midpoint_dist_of_subset,
    `Kakeya.Assouad.ordinary_capsule_pair_center_height,
    `Kakeya.Assouad.ordinary_capsule_pair_parameter_bounds,
    `Kakeya.Assouad.fin_grid_interval_count_mul_add,
    `Kakeya.Assouad.longitudinalTubeGrid_center_count,
    `Kakeya.Assouad.longitudinalTubeGrid_fine_count,
    `Kakeya.Assouad.longitudinalTubeGrid_tubeWolff,
    `Kakeya.Assouad.longitudinalTubeGrid_ordinary_distinct,
    `Kakeya.Assouad.longitudinalTubeGrid_in_unitBall,
    `Kakeya.Assouad.longitudinalTubeGrid_projection_volume,
    `Kakeya.Assouad.exists_normalized_ordinary_tubeWolff_longitudinal_counterexample,
    `Kakeya.Assouad.not_pureWZ2NormalizedOrdinaryTubeWolffProjectionStatement,
    `Kakeya.Assouad.dilatedTubeWolffVolumeBound_one_iff,
    `Kakeya.Assouad.dilatedTubeWolffVolumeBound_of_bodyConvexWolffBound,
    `Kakeya.Assouad.dilatedTubeWolffVolumeBound_of_convexWolffBound,
    `Kakeya.Assouad.fullLineTubeInBall_subset_dilated32,
    `Kakeya.Assouad.dilated32_volume_le,
    `Kakeya.Assouad.tubeParameterFrostmanBound_of_dilatedTubeWolffBound,
    `Kakeya.Assouad.pure_wz2_proposition7_1_dilated_tube_wolff,
    `Kakeya.Assouad.pure_wz2_dilated_tube_wolff_lower_bound_in_vertical_chart,
    `Kakeya.Assouad.pure_wz2_dilated_tube_wolff_lower_bound_in_unit_ball,
    `Kakeya.Assouad.pure_wz2_convex_wolff_lower_bound_via_dilated_tubes,
    `Kakeya.Assouad.pure_wz2_convex_wolff_lower_bound_in_unit_ball_via_dilated_tubes,
    `Kakeya.Assouad.pure_wz2_no_critical_package_of_normalized_projection,
    `Kakeya.Assouad.PureWZ2Theorem5_2Unconditional]
  for name in names do
    let info ← getConstInfo name
    let axioms ← collectAxioms name
    for ax in axioms do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Nonstandard axiom {ax} in {name}"
    let statement ← liftTermElabM <| Meta.ppExpr info.type
    liftIO <| IO.println <| "CORE_AXIOMS " ++ (Json.mkObj [
      ("name", toJson name.toString),
      ("axioms", toJson (axioms.map Name.toString)),
      ("type", toJson statement.pretty)]).compress

run_cmd do
  -- These names must exist even when deliberately absent from a root's value closure.
  for name in #[`Kakeya.Assouad.pureWZ2_node7_affine_diagonal_preparation,
                `Kakeya.Assouad.pure_wz2_node08_theorem5_2,
                `Kakeya.Assouad.tubeWolffBound_of_convexWolffBound,
                `Kakeya.Assouad.tubeParameterFrostmanBound_of_convexWolffBound] do
    let _ ← getConstInfo name
    liftIO <| IO.println <| "CORE_CONSTANT " ++ (toJson name.toString).compress

run_cmd do
  let inputs := #[
    (`Kakeya.Assouad.pureWZ2_frameProjectedNormal_lower_of_long_axis, "haxis"),
    (`Kakeya.Assouad.pureWZ2_frameProjectedNormal_lower_of_long_axis, "hframe"),
    (`Kakeya.Assouad.pureWZ2_dense_short_global_grain_normal, "hloss"),
    (`Kakeya.Assouad.pureWZ2_dense_short_global_grain_normal, "hgap"),
    (`Kakeya.Assouad.pureWZ2_prescribed_slab_frame_preparation, "hmassGap"),
    (`Kakeya.Assouad.pureWZ2_dense_cell_label_refinement, "hcap"),
    (`Kakeya.Assouad.pureWZ2_dense_cell_label_refinement, "hbudget"),
    (`Kakeya.Assouad.pure_wz2_lemma66_normalized_interval, "hbudget"),
    (`Kakeya.Assouad.pureWZ2_hierarchy_initial_reentrant_source_production_with_kernel, "kernel"),
    (`Kakeya.Assouad.PureWZ2.proposition63_m9_pre_node3_cutoff_with_kernel, "kernel"),
    (`Kakeya.Assouad.PureWZ2.proposition63_m9_two_call_robust_schedule_of_second_with_kernel, "kernel"),
    (`Kakeya.Assouad.pureWZ2_c2_grains_from_reentrant, "grains"),
    (`Kakeya.Assouad.pureWZ2_c2_source_with_fine_cap, "hc2grains"),
    (`Kakeya.Assouad.pureWZ2_c2_source_with_fine_cap, "certifiedProvider"),
    (`Kakeya.Assouad.pureWZ2_interval_ready_c2_source, "hc2grains"),
    (`Kakeya.Assouad.pureWZ2_interval_ready_c2_source, "certifiedProvider"),
    (`Kakeya.Assouad.pureWZ2_c2_source_with_prescribed_intervals, "hc2grains"),
    (`Kakeya.Assouad.pureWZ2_c2_source_with_prescribed_intervals, "certifiedProvider"),
    (`Kakeya.Assouad.pureWZ2PrescribedSlabHull_cover, "hcover"),
    (`Kakeya.Assouad.pureWZ2PrescribedSlabHull_multiplicity, "hcap"),
    (`Kakeya.Assouad.TubeWolffBound.to_ordinaryVolume, "hF"),
    (`Kakeya.Assouad.OrdinaryTubeWolffVolumeBound.to_radiusSquared, "hF"),
    (`Kakeya.Assouad.tubeParameterFrostmanBound_of_commonHeightTubeWolffBound, "hmodel"),
    (`Kakeya.Assouad.tubeParameterFrostmanBound_of_commonHeightTubeWolffBound, "hwolff"),
    (`Kakeya.Assouad.tubeParameterFrostmanBound_of_commonHeightOrdinaryTubeWolff, "hmodel"),
    (`Kakeya.Assouad.tubeParameterFrostmanBound_of_commonHeightOrdinaryTubeWolff, "hwolff"),
    (`Kakeya.Assouad.ordinaryTubeWolffVolumeBound_of_convexWolffBound, "hcwa"),
    (`Kakeya.Assouad.pure_wz2_node7b_common_height_from_retained_large_slope, "largeSlope"),
    (`Kakeya.Assouad.pure_wz2_no_critical_package_of_common_height_projection, "upper"),
    (`Kakeya.Assouad.pureWZ2_direct_halfOffset_large_slope_retained, "hC2"),
    (`Kakeya.Assouad.pure_wz2_node7_from_large_slope, "largeSlope"),
    (`Kakeya.Assouad.pure_wz2_node7b_normalized_from_retained_large_slope, "largeSlope"),
    (`Kakeya.Assouad.slopeOffsetRetubedFamily_cwa, "hC"),
    (`Kakeya.Assouad.slopeOffsetSlabShading_dense, "hdense"),
    (`Kakeya.Assouad.tubeParameterFrostmanBound_of_fullLineTubeWolffBound, "hwolff"),
    (`Kakeya.Assouad.grid_os_bounded_one_scale_sharp_from_positive, "hPositive"),
    (`Kakeya.Assouad.tubeParameterFrostman_to_centered_tubeWolff, "hF"),
    (`Kakeya.Assouad.tubeParameterFrostman_to_centered_tubeWolff, "hsegments"),
    (`Kakeya.Assouad.offsetObstruction_projection_subset, "hplane"),
    (`Kakeya.Assouad.offsetObstruction_projection_subset, "hwindow"),
    (`Kakeya.Assouad.ordinary_capsule_midpoint_dist_of_subset, "hST"),
    (`Kakeya.Assouad.ordinary_capsule_pair_parameter_bounds, "hST"),
    (`Kakeya.Assouad.ordinary_capsule_pair_parameter_bounds, "hUT"),
    (`Kakeya.Assouad.longitudinalTubeGrid_tubeWolff, "hn"),
    (`Kakeya.Assouad.exists_normalized_ordinary_tubeWolff_longitudinal_counterexample, "heta"),
    (`Kakeya.Assouad.exists_normalized_ordinary_tubeWolff_longitudinal_counterexample, "hcutoff"),
    (`Kakeya.Assouad.dilatedTubeWolffVolumeBound_of_bodyConvexWolffBound, "hcwa"),
    (`Kakeya.Assouad.dilatedTubeWolffVolumeBound_of_convexWolffBound, "hcwa"),
    (`Kakeya.Assouad.fullLineTubeInBall_subset_dilated32, "hbase"),
    (`Kakeya.Assouad.tubeParameterFrostmanBound_of_dilatedTubeWolffBound, "hbase"),
    (`Kakeya.Assouad.tubeParameterFrostmanBound_of_dilatedTubeWolffBound, "hvertical"),
    (`Kakeya.Assouad.tubeParameterFrostmanBound_of_dilatedTubeWolffBound, "hwolff"),
    (`Kakeya.Assouad.pure_wz2_no_critical_package_of_normalized_projection, "upper")]
  for (name, wanted) in inputs do
    let info ← getConstInfo name
    let some value := info.value? (allowOpaque := true)
      | throwError "No proof body for {name}"
    let count ← liftTermElabM <| lambdaTelescope value fun xs body => do
      let mut found := false
      let mut total := 0
      for x in xs do
        let localDecl ← x.fvarId!.getDecl
        if localDecl.userName.toString == wanted then
          found := true
          let counter ← IO.mkRef (0 : Nat)
          body.forEach fun subterm => do
            if let .app fn arg := subterm then
              if fn == x || arg == x then counter.modify (· + 1)
            pure ()
          total := total + (← counter.get)
      unless found do throwError "Binder {wanted} not found in {name}"
      return total
    unless count > 0 do throwError "Unused upstream proof argument {wanted} in {name}"
    liftIO <| IO.println <| "CORE_BINDER " ++ (Json.mkObj [
      ("name", toJson name.toString), ("binder", toJson wanted),
      ("applications", toJson count)]).compress
