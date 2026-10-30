#!/usr/bin/env python3
"""Audit Core proof-value paths after check.py --lean and core_contracts.lean.

This checks the implemented normalized route.  The explicit missing paper
transports below are not converted into passing mathematical requirements.
"""

from collections import deque
import json
from pathlib import Path
import re
import subprocess

from dependencies import EXTRACTOR, RAW, THEOREM, read_graph

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / "blueprint/build/core-integration"
NS = "Kakeya.Assouad."
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def add_supplementary_graphs(graph):
    """Compile separate closures for proved APIs outside the final root.

    The blueprint graph deliberately contains only its final root's closure.
    Do not insert dummy references into that proof to make other APIs reachable.
    """
    roots = [NS + "pure_wz2_convex_wolff_lower_bound_in_unit_ball",
             NS + "PureWZ2PaperTerminalProjectionRefinement.projection_volume_le",
             NS + "not_pureWZ2UnrestrictedTubeWolffProjectionStatement",
             NS + "not_pureWZ2NormalizedOrdinaryTubeWolffProjectionStatement",
             NS + "pure_wz2_left_line_c2_prescribed_intervals",
             NS + "TubeWolffBound.to_ordinaryVolume",
             NS + "pure_wz2_no_critical_package_of_normalized_projection",
             NS + "pure_wz2_left_line_normalized_projection",
             NS + "pure_wz2_ordinary_tube_wolff_lower_bound_in_unit_ball",
             NS + "pure_wz2_convex_wolff_lower_bound_via_dilated_tubes",
             NS + "pure_wz2_convex_wolff_lower_bound_in_unit_ball_via_dilated_tubes",
             NS + "pure_wz2_lemma66_prescribed_interval",
             NS + "pureWZ2_interval_ready_c2_source"]
    libraries = [name for name, row in graph.items() if row.get("scope") == "library"]
    array = lambda names: "#[" + ", ".join(json.dumps(n) + ".toName" for n in names) + "]"
    driver = OUT / "SupplementaryCoreDependencies.lean"
    # Use exactly the root audit's imports and order. The repository has
    # independently compiled, same-name helper theorems (including AD
    # translation); a smaller import environment can select another proof
    # of the same proposition. Never merge graphs from those environments.
    modules = [line.strip() for line in (ROOT / "blueprint/lean-imports.txt").read_text().splitlines()
               if line.strip() and not line.lstrip().startswith("#")]
    code = ("".join(f"import {module}\n" for module in modules) +
            "import Lean\n\n" + EXTRACTOR.read_text() + "\n")
    outputs = []
    for i, root in enumerate(roots):
        output = OUT / f"supplementary-dependencies-{i}.jsonl"
        outputs.append(output)
        code += (f"run_cmd BlueprintDependencies.collect {json.dumps(root)}.toName "
                 f"{array(['MyLeanRepo', 'Kakeya', 'FinalCheck', 'Comparator'])} "
                 f"{json.dumps(str(output))} {array(libraries)}\n")
    driver.write_text(code)
    with (OUT / "supplementary-dependencies.log").open("w") as log:
        subprocess.run(["lake", "env", "lean", str(driver)], cwd=ROOT,
                       stdout=log, stderr=subprocess.STDOUT, check=True)
    for root, output in zip(roots, outputs):
        header, extra, _ = read_graph(output)
        assert header["root"] == root
        for name, row in extra.items():
            if name in graph:
                for kind in ["type", "value", "structural", "module", "scope", "kind", "line"]:
                    assert row[kind] == graph[name][kind], f"Inconsistent kernel data: {name}"
            else:
                graph[name] = row
    return roots


def walk(graph, source):
    if source not in graph:
        raise AssertionError(f"No compiled source for dependency audit: {source}")
    previous = {source: None}
    pending = deque([source])
    while pending:
        node = pending.popleft()
        for target in graph[node]["value"]:
            if target not in previous:
                previous[target] = node
                pending.append(target)
    return previous


def route(previous, target):
    if target not in previous:
        return None
    result = []
    while target is not None:
        result.append(target)
        target = previous[target]
    return list(reversed(result))


def uncomment(source):
    """Remove nested Lean block comments, line comments, and string literals."""
    result = []
    i = 0
    depth = 0
    while i < len(source):
        if source.startswith("/-", i):
            depth += 1
            i += 2
        elif depth and source.startswith("-/", i):
            depth -= 1
            i += 2
        elif depth:
            i += 1
        elif source.startswith("--", i):
            i = source.find("\n", i)
            if i == -1:
                break
        elif source[i] == '"':
            i += 1
            while i < len(source):
                if source[i] == "\\":
                    i += 2
                elif source[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
            result.append(" ")
        else:
            result.append(source[i])
            i += 1
    return "".join(result)


def main():
    _, graph, _ = read_graph(RAW)
    root_graph_size = len(graph)
    supplementary_roots = add_supplementary_graphs(graph)
    log = (OUT / "core-contracts.log").read_text()
    assert "error:" not in log, "Core contracts did not compile"
    axioms = [json.loads(line.removeprefix("CORE_AXIOMS "))
              for line in log.splitlines() if line.startswith("CORE_AXIOMS ")]
    binders = [json.loads(line.removeprefix("CORE_BINDER "))
               for line in log.splitlines() if line.startswith("CORE_BINDER ")]
    known = set(graph) | {row["name"] for row in axioms} | {
        json.loads(line.removeprefix("CORE_CONSTANT "))
        for line in log.splitlines() if line.startswith("CORE_CONSTANT ")}
    assert len(axioms) == 105 and len(binders) == 53, "Incomplete Lean audit"
    assert all(set(row["axioms"]) <= ALLOWED for row in axioms)
    assert all(row["applications"] > 0 for row in binders)
    normalized_interval_type = next(row["type"] for row in axioms
                                    if row["name"] == NS + "pure_wz2_lemma66_normalized_interval")
    assert "PureWZ2C2GrainConfiguration" in normalized_interval_type
    assert "FrameNormalCompatibility" not in normalized_interval_type
    assert "PureWZ2CriticalPackage" not in normalized_interval_type

    pairs = [
        ("pure_wz2_lemma66_normalized_interval", "pureWZ2_prescribed_slab_frame_preparation"),
        ("pure_wz2_lemma66_normalized_interval", "pure_wz2_lemma66_prepared_interval_on"),
        ("pure_wz2_lemma66_normalized_interval", "pureWZ2PrescribedSlabHull_mass"),
        ("pure_wz2_lemma66_normalized_interval", "pureWZ2PrescribedSlabHull_cover"),
        ("pure_wz2_lemma66_normalized_interval", "pureWZ2PrescribedSlabHull_multiplicity"),
        ("pureWZ2_prescribed_slab_frame_preparation", "pureWZ2_dense_short_global_grain_normal"),
        ("pureWZ2_prescribed_slab_frame_preparation", "pureWZ2_dense_cell_label_refinement"),
        ("pureWZ2_prescribed_slab_frame_preparation", "pureWZ2_short_grain_label_count"),
        ("pureWZ2_prescribed_slab_frame_preparation", "pureWZ2_short_grain_packet_geometry"),
        ("pureWZ2_dense_short_global_grain_normal", "paper_tube_segment_ad_direction_bound"),
        ("pureWZ2_dense_short_global_grain_normal", "pureWZ2ShortGlobalGrain_subset_segment"),
        ("pureWZ2_dense_short_global_grain_normal", "pureWZ2ShortGlobalGrain_dist"),
        ("pureWZ2_dense_short_global_grain_normal", "pureWZ2_frameProjectedNormal_lower_of_long_axis"),
        ("pureWZ2_dense_cell_label_refinement", "mass_le_of_pointMultiplicity_le"),
        ("pureWZ2_short_grain_label_count", "pureWZ2_globalBinsAtHeight_card_bound"),
        ("pure_wz2_lemma66_prepared_interval_on", "PureWZ2Lemma31SlabAssembly.derivative_lower"),
        ("pure_wz2_lemma66_prepared_interval", "pure_wz2_lemma66_prepared_interval_on"),
        ("PureWZ2Lemma31SlabAssembly.derivative_lower", "pureWZ2_faithful_step4_producer_of_frame_lower"),
        ("PureWZ2Theorem5_2Unconditional", "pure_wz2_theorem5_2_of_common_height_projection"),
        ("PureWZ2Theorem5_2Unconditional", "pure_wz2_left_line_common_height_projection"),
        ("PureWZ2Theorem5_2Unconditional", "pure_wz2_convex_wolff_lower_bound_in_common_height_chart"),
        ("pure_wz2_left_line_common_height_projection", "PureWZ2PaperTerminalProjectionRefinement.common_height"),
        ("pure_wz2_left_line_common_height_projection", "pure_wz2_paper_terminal_normalization_cutoff"),
        ("pure_wz2_convex_wolff_lower_bound_in_common_height_chart", "ordinaryTubeWolffVolumeBound_of_convexWolffBound"),
        ("pure_wz2_convex_wolff_lower_bound_in_common_height_chart", "pure_wz2_proposition7_1_ordinary_tube_wolff"),
        ("pure_wz2_proposition7_1_ordinary_tube_wolff", "OrdinaryTubeWolffVolumeBound.to_radiusSquared"),
        ("pure_wz2_proposition7_1_ordinary_tube_wolff", "tubeParameterFrostmanBound_of_commonHeightTubeWolffBound"),
        ("pure_wz2_proposition7_1_ordinary_tube_wolff", "pure_wz2_proposition7_1_parameter_frostman"),
        ("tubeParameterFrostmanBound_of_commonHeightTubeWolffBound", "commonHeight_modelTube_carrier_subset"),
        ("commonHeight_modelTube_carrier_subset", "commonHeight_segment_point_dist"),
        ("commonHeight_segment_point_dist", "commonHeight_axisPoint_dist"),
        ("commonHeight_segment_point_dist", "commonHeight_direction_dist"),
        ("pure_wz2_ordinary_tube_wolff_lower_bound_in_unit_ball", "pure_wz2_proposition7_1_ordinary_tube_wolff"),
        ("pure_wz2_ordinary_tube_wolff_lower_bound_in_unit_ball", "PureWZ2.wz2_ed_packing_bound"),
        ("pure_wz2_no_critical_package_of_normalized_projection", "pure_wz2_convex_wolff_lower_bound_in_vertical_chart"),
        ("pure_wz2_left_line_c2_grains", "pure_wz2_node04_reentrant_grains"),
        ("pure_wz2_node04_reentrant_grains", "pure_wz2_node03_rich_prop62_kernel"),
        ("pure_wz2_left_line_c2_grains", "pureWZ2_c2_grains_from_reentrant"),
        ("PureWZ2Theorem5_2Unconditional", "pureWZ2_c2_source_with_fine_cap"),
        ("pure_wz2_left_line_c2_prescribed_intervals", "pure_wz2_left_line_c2_grains"),
        ("pure_wz2_left_line_c2_prescribed_intervals", "pureWZ2_c2_grains_from_reentrant"),
        ("pure_wz2_left_line_c2_prescribed_intervals", "pureWZ2_c2_source_with_fine_cap"),
        ("pureWZ2_interval_ready_c2_source", "pureWZ2_node6_fixed_sqrt_assembly_with_source_property"),
        ("pure_wz2_left_line_c2_prescribed_intervals", "pure_wz2_lemma66_normalized_interval"),
        ("pure_wz2_left_line_c2_prescribed_intervals", "pureWZ2_prescribed_slab_frame_preparation"),
        ("pure_wz2_lemma66_prescribed_interval", "pureWZ2PrescribedSlabHull_mass"),
        ("pure_wz2_lemma66_prescribed_interval", "pureWZ2PrescribedSlabHull_cover"),
        ("pure_wz2_lemma66_prescribed_interval", "pureWZ2PrescribedSlabHull_multiplicity"),
        ("pure_wz2_lemma66_prescribed_interval", "pureWZ2PrescribedSlabHull_height"),
        ("pure_wz2_lemma66_prescribed_interval", "pure_wz2_lemma66_prepared_interval"),
        ("pureWZ2PrescribedSlabHull_mass", "pureWZ2PrescribedSlabHull_contains"),
        ("pureWZ2PrescribedSlabHull_multiplicity", "pureWZ2PrescribedSlabHull_witness"),
        ("pure_wz2_left_line_normalized_projection", "pure_wz2_lemma66_prepared_interval"),
        ("pure_wz2_lemma66_prepared", "pure_wz2_lemma66_prepared_interval"),
        ("pure_wz2_lemma66_prepared_interval", "large_slope_faithful_convex_overload"),
        ("pure_wz2_left_line_normalized_projection", "pure_wz2_node7_analytic_cleanup_with_cwa"),
        ("pure_wz2_left_line_normalized_projection", "pure_wz2_paper_terminal_normalization_cutoff"),
        ("pure_wz2_left_line_normalized_projection", "exists_actual_terminal_slope_offset_cutoff_for_output_loss"),
        ("pure_wz2_node7b_normalized_from_retained_large_slope", "PureWZ2LargeSlopeConstruction.toLargeSlopeConfiguration"),
        ("pure_wz2_paper_terminal_normalization_cutoff", "slopeOffsetSlabShading_dense"),
        ("pure_wz2_paper_terminal_normalization_cutoff", "slopeOffsetRetubedFamily_cwa"),
        ("pure_wz2_paper_terminal_normalization_cutoff", "slopeOffsetSlabShading_projection"),
        ("pure_wz2_paper_terminal_normalization_cutoff", "exists_slopeOffset_mass_slab"),
        ("pure_wz2_paper_terminal_normalization_cutoff", "slopeOffsetLinear_axis_image"),
        ("slopeOffsetRetubedFamily_cwa", "wz2PaperBodyConvexWolffBound_of_affineTransport"),
        ("slopeOffsetSlabShading_projection", "slopeOffset_twisted_volume"),
        ("PureWZ2PaperTerminalProjectionRefinement.projection_volume_le", "slopeOffset_twisted_volume"),
        ("pure_wz2_node7_analytic_cleanup_with_cwa", "deltaMax_to_normalized_convexWolff"),
        ("pure_wz2_convex_wolff_lower_bound_in_vertical_chart", "fullLineTubeWolffBound_of_convexWolffBound"),
        ("pure_wz2_convex_wolff_lower_bound_in_vertical_chart", "pure_wz2_full_line_tube_wolff_lower_bound_in_vertical_chart"),
        ("pure_wz2_convex_wolff_lower_bound_in_vertical_chart", "pure_wz2_proposition7_1_full_line_tube_wolff"),
        ("pure_wz2_convex_wolff_lower_bound_in_unit_ball", "fullLineTubeWolffBound_of_bodyConvexWolffBound"),
        ("pure_wz2_convex_wolff_lower_bound_in_unit_ball", "pure_wz2_proposition7_1_full_line_tube_wolff"),
        ("pure_wz2_proposition7_1_full_line_tube_wolff", "tubeParameterFrostmanBound_of_fullLineTubeWolffBound"),
        ("pure_wz2_proposition7_1_full_line_tube_wolff", "pure_wz2_proposition7_1_parameter_frostman"),
        ("tubeParameterFrostmanBound_of_fullLineTubeWolffBound", "fullLineTubeInBall_six_volume_le"),
        ("TubeWolffBound.to_ordinaryVolume", "ordinaryTube_not_subset_of_radius_lt"),
        ("TubeWolffBound.to_ordinaryVolume", "ordinaryTube_radius_sq_le_volume"),
        ("OrdinaryTubeWolffVolumeBound.to_radiusSquared", "ordinaryTube_volume_le_ten_radius_sq"),
        ("ordinaryTube_not_subset_of_radius_lt", "ordinaryTube_volume_eq"),
        ("pure_wz2_proposition7_1_parameter_frostman", "pure_wz2_lemma7_12_parameter_frostman_sharp_density"),
        ("pure_wz2_proposition7_1_parameter_frostman", "grid_os_finite_run"),
        ("pure_wz2_proposition7_1_parameter_frostman", "grid_os_telescoping"),
        ("pure_wz2_lemma7_12_parameter_frostman_sharp_density", "projected_fiber_os_preparation_with_density"),
        ("pure_wz2_lemma7_12_parameter_frostman_sharp_density", "parameter_block_projection_uniformization_from_os_with_density"),
        ("pure_wz2_lemma7_12_parameter_frostman_sharp_density", "parameter_block_positive_window_assembly_with_density"),
        ("pure_wz2_lemma7_12_parameter_frostman_sharp_density", "grid_os_bounded_one_scale_sharp_from_positive"),
        ("pure_wz2_lemma7_12_parameter_frostman_sharp_density", "parameter_block_representative_cinematic_pullback"),
        ("pure_wz2_lemma7_12_parameter_frostman_sharp_density", "half_parameter_cinematic_pyz_general"),
        ("not_pureWZ2UnrestrictedTubeWolffProjectionStatement", "exists_ordinary_tubeWolff_slope_offset_counterexample"),
        ("exists_ordinary_tubeWolff_slope_offset_counterexample", "planarTubeGrid_in_unitBall"),
        ("exists_ordinary_tubeWolff_slope_offset_counterexample", "planarTubeGrid_ordinary_distinct"),
        ("exists_ordinary_tubeWolff_slope_offset_counterexample", "planarTubeGrid_tubeWolff"),
        ("exists_ordinary_tubeWolff_slope_offset_counterexample", "planarTubeGrid_projection_sqrt"),
        ("planarTubeGrid_tubeWolff", "tubeParameterFrostman_to_centered_tubeWolff"),
        ("planarTubeGrid_tubeWolff", "planarTubeGrid_parameter_frostman"),
        ("planarTubeGrid_projection_sqrt", "offsetObstruction_projection_volume_le"),
        ("not_pureWZ2NormalizedOrdinaryTubeWolffProjectionStatement", "exists_normalized_ordinary_tubeWolff_longitudinal_counterexample"),
        ("exists_normalized_ordinary_tubeWolff_longitudinal_counterexample", "longitudinalTubeGrid_in_unitBall"),
        ("exists_normalized_ordinary_tubeWolff_longitudinal_counterexample", "longitudinalTubeGrid_ordinary_distinct"),
        ("exists_normalized_ordinary_tubeWolff_longitudinal_counterexample", "longitudinalTubeGrid_tubeWolff"),
        ("exists_normalized_ordinary_tubeWolff_longitudinal_counterexample", "longitudinalTubeGrid_projection_volume"),
        ("exists_normalized_ordinary_tubeWolff_longitudinal_counterexample", "TubeWolffBound.to_ordinaryVolume"),
        ("longitudinalTubeGrid_tubeWolff", "ordinary_capsule_pair_parameter_bounds"),
        ("longitudinalTubeGrid_tubeWolff", "ordinary_capsule_pair_center_height"),
        ("longitudinalTubeGrid_tubeWolff", "longitudinalTubeGrid_center_count"),
        ("longitudinalTubeGrid_tubeWolff", "longitudinalTubeGrid_fine_count"),
        ("longitudinalTubeGrid_center_count", "fin_grid_interval_count_mul_add"),
        ("ordinary_capsule_pair_center_height", "ordinary_capsule_midpoint_dist_of_subset"),
        ("longitudinalTubeGrid_ordinary_distinct", "longitudinalTubeGrid_eq_of_centered_containment"),
        ("pure_wz2_convex_wolff_lower_bound_via_dilated_tubes", "dilatedTubeWolffVolumeBound_of_convexWolffBound"),
        ("pure_wz2_convex_wolff_lower_bound_via_dilated_tubes", "pure_wz2_proposition7_1_dilated_tube_wolff"),
        ("pure_wz2_convex_wolff_lower_bound_in_unit_ball_via_dilated_tubes", "dilatedTubeWolffVolumeBound_of_bodyConvexWolffBound"),
        ("pure_wz2_convex_wolff_lower_bound_in_unit_ball_via_dilated_tubes", "pure_wz2_dilated_tube_wolff_lower_bound_in_unit_ball"),
        ("pure_wz2_dilated_tube_wolff_lower_bound_in_unit_ball", "PureWZ2.wz2_ed_packing_bound"),
        ("pure_wz2_dilated_tube_wolff_lower_bound_in_vertical_chart", "essentially_distinct_card_bound_fixed_ball"),
        ("pure_wz2_proposition7_1_dilated_tube_wolff", "tubeParameterFrostmanBound_of_dilatedTubeWolffBound"),
        ("pure_wz2_proposition7_1_dilated_tube_wolff", "pure_wz2_proposition7_1_parameter_frostman"),
        ("tubeParameterFrostmanBound_of_dilatedTubeWolffBound", "fullLineTubeInBall_subset_dilated32"),
        ("tubeParameterFrostmanBound_of_dilatedTubeWolffBound", "dilated32_volume_le"),
        ("tubeParameterFrostmanBound_of_dilatedTubeWolffBound", "parameter_cluster_carrier_subset_widePrism"),
        ("dilated32_volume_le", "ordinaryTube_volume_le_ten_radius_sq"),
        ("dilated32_volume_le", "wz2_paper_centeredDilatedCarrier_volume"),
    ]
    cache = {}
    paths = []
    for a, b in pairs:
        source, target = NS + a, NS + b
        if source not in cache:
            cache[source] = walk(graph, source)
        previous = cache[source]
        value_path = route(previous, target)
        assert value_path, f"Missing proof-value path: {source} -> {target}"
        paths.append({"from": source, "to": target, "value_path": value_path})
    source = NS + "half_parameter_cinematic_pyz_general"
    previous = walk(graph, source)
    target = "Kakeya.Cinematic.wz2_uniformC2_input"
    value_path = route(previous, target)
    assert value_path, "Missing actual cinematic theorem call"
    paths.append({"from": source, "to": target, "value_path": value_path})

    # A body path through an already final theorem must not prove either side.
    absent = []
    for source in ["pure_wz2_left_line_normalized_projection",
                   "pure_wz2_convex_wolff_lower_bound_in_unit_ball",
                   "pure_wz2_convex_wolff_lower_bound_in_vertical_chart",
                   "not_pureWZ2UnrestrictedTubeWolffProjectionStatement",
                   "not_pureWZ2NormalizedOrdinaryTubeWolffProjectionStatement",
                   "pure_wz2_left_line_c2_prescribed_intervals",
                   "pure_wz2_lemma66_prescribed_interval",
                   "pure_wz2_lemma66_normalized_interval",
                   "pureWZ2_prescribed_slab_frame_preparation",
                   "TubeWolffBound.to_ordinaryVolume",
                   "OrdinaryTubeWolffVolumeBound.to_radiusSquared",
                   "pure_wz2_left_line_common_height_projection",
                   "pure_wz2_proposition7_1_ordinary_tube_wolff",
                   "pure_wz2_convex_wolff_lower_bound_in_common_height_chart",
                   "pure_wz2_ordinary_tube_wolff_lower_bound_in_unit_ball",
                   "pure_wz2_convex_wolff_lower_bound_via_dilated_tubes",
                   "pure_wz2_convex_wolff_lower_bound_in_unit_ball_via_dilated_tubes",
                   "pure_wz2_proposition7_1_dilated_tube_wolff",
                   "tubeParameterFrostmanBound_of_dilatedTubeWolffBound"]:
        previous = walk(graph, NS + source)
        for target in [THEOREM, NS + "pure_wz2_node08_theorem5_2"]:
            assert target in known, f"Unknown absence-check target: {target}"
            assert target not in previous, f"Circular proof route from {source}"
            absent.append({"from": NS + source, "to": target})
    # The supplied-configuration lemma must not silently replace its input
    # by a newly constructed C2 source or invoke the downstream large slope.
    source = NS + "pure_wz2_lemma66_normalized_interval"
    previous = walk(graph, source)
    for target in ["pure_wz2_left_line_c2_grains",
                   "pureWZ2_c2_source_with_fine_cap",
                   "pureWZ2_node6_fixed_sqrt_assembly_with_source_property",
                   "pure_wz2_node06_large_slope_retained",
                   "pure_wz2_proposition7_1_ordinary_tube_wolff"]:
        assert NS + target in known
        assert NS + target not in previous, f"Invalid supplied-configuration proof route: {target}"
        absent.append({"from": source, "to": NS + target})
    right = walk(graph, NS + "pure_wz2_convex_wolff_lower_bound_in_vertical_chart")
    for target in ["pure_wz2_left_line_normalized_projection",
                   "pure_wz2_node06_large_slope_retained",
                   "tubeParameterFrostmanBound_of_convexWolffBound",
                   "tubeWolffBound_of_convexWolffBound"]:
        assert NS + target in known, f"Unknown absence-check target: {target}"
        assert NS + target not in right
        absent.append({"from": NS + "pure_wz2_convex_wolff_lower_bound_in_vertical_chart",
                       "to": NS + target})
    # The actual-terminal path must not quietly return to the old independent branch.
    left = walk(graph, NS + "pure_wz2_left_line_normalized_projection")
    target = NS + "pureWZ2_node7_affine_diagonal_preparation"
    assert target in known, f"Unknown absence-check target: {target}"
    assert target not in left
    absent.append({"from": NS + "pure_wz2_left_line_normalized_projection", "to": target})
    # The physical Tube Wolff theorem is independent of every CWA lower bound.
    source = NS + "pure_wz2_proposition7_1_full_line_tube_wolff"
    physical = walk(graph, source)
    for target in [THEOREM, NS + "pure_wz2_convex_wolff_lower_bound_in_vertical_chart",
                   NS + "fullLineTubeWolffBound_of_convexWolffBound",
                   NS + "tubeParameterFrostmanBound_of_convexWolffBound",
                   NS + "pure_wz2_left_line_normalized_projection"]:
        assert target in known, f"Unknown absence-check target: {target}"
        assert target not in physical, f"Invalid dependency of Tube Wolff theorem: {target}"
        absent.append({"from": source, "to": target})

    # The obstruction is independently checked and is not inserted in the final proof.
    for obstruction in [NS + "not_pureWZ2UnrestrictedTubeWolffProjectionStatement",
                        NS + "not_pureWZ2NormalizedOrdinaryTubeWolffProjectionStatement"]:
        for source in [THEOREM, NS + "pure_wz2_proposition7_1_full_line_tube_wolff",
                       NS + "pure_wz2_proposition7_1_ordinary_tube_wolff",
                       NS + "pure_wz2_convex_wolff_lower_bound_in_common_height_chart",
                       NS + "pure_wz2_left_line_common_height_projection",
                       NS + "pure_wz2_proposition7_1_dilated_tube_wolff",
                       NS + "pure_wz2_convex_wolff_lower_bound_via_dilated_tubes",
                       NS + "pure_wz2_convex_wolff_lower_bound_in_unit_ball_via_dilated_tubes"]:
            assert obstruction in known
            assert obstruction not in walk(graph, source)
            absent.append({"from": source, "to": obstruction})

    # The longitudinal example does not borrow a CWA projection bound or the
    # actual left terminal to prove its negation.
    source = NS + "not_pureWZ2NormalizedOrdinaryTubeWolffProjectionStatement"
    previous = walk(graph, source)
    for target in ["pure_wz2_proposition7_1_ordinary_tube_wolff",
                   "pure_wz2_convex_wolff_lower_bound_in_common_height_chart",
                   "pure_wz2_left_line_common_height_projection"]:
        assert NS + target in known
        assert NS + target not in previous
        absent.append({"from": source, "to": NS + target})

    # The final root uses ordinary capsule tests. The old full-line theorem
    # remains verified as a separate API, without a proof-value path from root.
    for source in [THEOREM, NS + "pure_wz2_proposition7_1_ordinary_tube_wolff",
                   NS + "pure_wz2_convex_wolff_lower_bound_in_common_height_chart"]:
        previous = walk(graph, source)
        for target in ["pure_wz2_proposition7_1_full_line_tube_wolff",
                       "fullLineTubeWolffBound_of_convexWolffBound",
                       "tubeParameterFrostmanBound_of_convexWolffBound"]:
            assert NS + target in known, f"Unknown absence-check target: {target}"
            assert NS + target not in previous, f"Unexpected lower-bound route from {source}"
            absent.append({"from": source, "to": NS + target})
    ordinary = walk(graph, NS + "pure_wz2_proposition7_1_ordinary_tube_wolff")
    for target in ["pure_wz2_left_line_common_height_projection",
                   "ordinaryTubeWolffVolumeBound_of_convexWolffBound"]:
        assert NS + target in known
        assert NS + target not in ordinary
        absent.append({"from": NS + "pure_wz2_proposition7_1_ordinary_tube_wolff",
                       "to": NS + target})

    # The finite length-32 theorem derives its parameter count geometrically.
    # It must not borrow any CWA supplier, terminal, or earlier projection bound.
    source = NS + "pure_wz2_proposition7_1_dilated_tube_wolff"
    previous = walk(graph, source)
    for target in ["dilatedTubeWolffVolumeBound_of_convexWolffBound",
                   "dilatedTubeWolffVolumeBound_of_bodyConvexWolffBound",
                   "tubeParameterFrostmanBound_of_convexWolffBound",
                   "pure_wz2_proposition7_1_full_line_tube_wolff",
                   "pure_wz2_proposition7_1_ordinary_tube_wolff",
                   "pure_wz2_left_line_common_height_projection"]:
        assert NS + target in known
        assert NS + target not in previous
        absent.append({"from": source, "to": NS + target})

    # The new CWA endpoints actually pass through the finite-capsule theorem.
    for source in ["pure_wz2_convex_wolff_lower_bound_via_dilated_tubes",
                   "pure_wz2_convex_wolff_lower_bound_in_unit_ball_via_dilated_tubes"]:
        previous = walk(graph, NS + source)
        for target in ["pure_wz2_proposition7_1_full_line_tube_wolff",
                       "fullLineTubeWolffBound_of_convexWolffBound",
                       "tubeParameterFrostmanBound_of_convexWolffBound"]:
            assert NS + target in known
            assert NS + target not in previous
            absent.append({"from": NS + source, "to": NS + target})

    changed = set(subprocess.check_output(
        ["git", "diff", "--name-only", "-z"], cwd=ROOT).decode().split("\0"))
    changed.update(subprocess.check_output(
        ["git", "ls-files", "--others", "--exclude-standard", "-z"], cwd=ROOT
    ).decode().split("\0"))
    sources = sorted(p for p in changed if p.endswith(".lean"))
    for path in sources:
        assert not re.search(r"\b(sorry|admit|axiom|native_decide)\b",
                             uncomment((ROOT / path).read_text())), path
    result = {"status": "passed_for_implemented_scope",
              "root_project_graph_size": root_graph_size,
              "audited_graph_size": len(graph), "supplementary_roots": supplementary_roots,
              "axioms": axioms,
              "upstream_arguments": binders, "required_value_paths": paths,
              "absent_paths": absent, "checked_sources": sources,
              "refuted_claims": [{
                  "statement": NS + "PureWZ2UnrestrictedTubeWolffProjectionStatement",
                  "proof": NS + "not_pureWZ2UnrestrictedTubeWolffProjectionStatement",
                  "scope": "Uniform ordinary Tube Wolff projection bound with arbitrary f(0), even for nonempty, essentially distinct unit-ball families and full shading"}, {
                  "statement": NS + "PureWZ2NormalizedOrdinaryTubeWolffProjectionStatement",
                  "proof": NS + "not_pureWZ2NormalizedOrdinaryTubeWolffProjectionStatement",
                  "scope": "Uniform ordinary unit-segment capsule actual-volume Tube Wolff projection bound with arbitrary longitudinal centers, even for f(z)=z, bounded vertical chart, paper distinctness, unit-ball containment and full shading",
                  "construction": "delta=1/(4096 n^2), n^5 tubes, absolute Tube Wolff constant 2^60 and projected area at most 24 sqrt(delta)",
                  "limitation": "No CWA certificate; the common-height terminal and its final contradiction are unaffected. This separate model discrepancy is not an accepted scope correction."}],
              "accepted_scope_corrections": [{
                  "name": "Slope-offset normalization",
                  "remark": "rem:parameter-frostman",
                  "requirement": "Apply normalized Proposition 7.1/6.8 to the configuration transported from the actual left terminal, with the proved CWA, density, scale and area losses",
                  "evidence": NS + "pure_wz2_paper_terminal_normalization_cutoff",
                  "outside_adopted_scope": "Uniform lower bounds for arbitrarily supplied offsets without the actual-terminal normalization"}],
              "proved_additional_scope": [{
                  "name": "One constructed C2 source for every later prescribed interval",
                  "proof": NS + "pure_wz2_left_line_c2_prescribed_intervals",
                  "preparation": "Global fine multiplicity cap and frame constructed upstream; all occupied cells meeting the prescribed slab retain its mass and transfer the cover and cap",
                  "remaining_hypothesis": "Slab mass at least (pi/4) delta^(eta/16+2) #T |J|, with cover delta^(-eta/16) |J|^(-2+sigma) and 2000 eta <= epsilon sigma^2"}, {
                  "name": "Ordinary capsule radius-squared and actual-volume tests",
                  "proofs": [NS + "TubeWolffBound.to_ordinaryVolume",
                             NS + "OrdinaryTubeWolffVolumeBound.to_radiusSquared"],
                  "scope": "All positive coarse radii; constants C and 10 C. This does not convert arbitrary ordinary capsules to full-line tests."}, {
                  "name": "Ordinary Tube Wolff specialization on the actual common-height terminal",
                  "proof": NS + "pure_wz2_proposition7_1_ordinary_tube_wolff",
                  "geometry": "Radius-r parameter clusters fit in one radius-8r ordinary coarse capsule; factors 64 for radius-squared tests and 640 for actual-volume tests",
                  "terminal_evidence": NS + "PureWZ2PaperTerminalProjectionRefinement.common_height",
                  "final_route": "CWA -> ordinary capsule actual-volume Tube Wolff -> ordinary Proposition 7.1 -> parameter iteration, on the same common-height upper-bound configuration",
                  "scope": "Bounded vertical chart, common-height unit segments and normalized slope. The actual terminal satisfies these by proved construction. Arbitrarily supplied segments and charts are not covered."}, {
                  "name": "Finite coarse capsules with fixed longitudinal margin",
                  "proof": NS + "pure_wz2_proposition7_1_dilated_tube_wolff",
                  "model": "The given fine capsules have unit axes at arbitrary longitudinal positions; coarse capsules have axis length 32 and arbitrary positive physical radius",
                  "geometry": "A radius-r parameter cluster lies in one length-32, radius-20r capsule; the indexed parameter Frostman factor is 128000",
                  "cwa_endpoints": [NS + "pure_wz2_convex_wolff_lower_bound_via_dilated_tubes",
                                    NS + "pure_wz2_convex_wolff_lower_bound_in_unit_ball_via_dilated_tubes"],
                  "quantifiers": "Uniform cutoff before every family and longitudinal position; packing removes the cardinality premise; bounded vertical chart and normalized slope remain explicit",
                  "limitation": "CWA supplies the corrected coarse tests directly. No implication from literal unit-length Tube Wolff to these tests is asserted, and this is not silently treated as an accepted paper-scope correction."}],
              "not_proved": [
                  "Paper Lemma 6.6 from absolute slab mass delta^eta |J| and covering alone. The normalized lemma now accepts every supplied Prop. 6.4 configuration and derives slab frame control internally, but still requires mass (pi/4) delta^(eta/16+2) #T |J| and the slab cap delta^(2-sigma-eta/8192) #T; neither follows here from the printed hypotheses",
                  "Paper model and chart scope: literal unit-length ordinary Tube Wolff at arbitrary longitudinal centers is refuted. A finite length-32 coarse-test correction is proved for all bounded vertical-chart families and supplied by CWA, but its identification with the paper scope and transport beyond that chart are not established"]}
    (OUT / "core-proof-audit.json").write_text(json.dumps(result, indent=2) + "\n")
    print(f"PASS: {len(axioms)} axiom checks; {len(binders)} upstream arguments; "
          f"{len(paths)} proof-value paths; {len(absent)} absent paths; "
          f"{len(sources)} changed Lean source scans.")
    print("The actual terminal uses common-height ordinary capsules. Length-32 coarse capsules now give a separate CWA projection route for arbitrary longitudinal positions. General Lemma 6.6 and the remaining paper-model/chart scope are unresolved; literal unit-length arbitrary-longitudinal Tube Wolff is refuted.")


if __name__ == "__main__":
    main()
