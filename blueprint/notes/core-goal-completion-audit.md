# Core goal completion audit — 2026-10-30

The **adopted constructive Core route is complete and verified**. Following
the user's instruction to record the Prop. 7.1 model difference as a
Remark and finish the goal, the final proof now uses the finite length-32
coarse-capsule theorem. It permits arbitrary longitudinal positions of
the original fine unit segments. CWA supplies the corrected tests on the
same normalized left-terminal configuration used for the upper bound.

This is a completion of the proof route with its stated intermediate
scopes. It does not assert every generic printed lemma. The prepared
Lemma 6.6 used by Proposition 6.5 has its prerequisites proved upstream;
the extension from the printed absolute mass and cover alone remains a
literature gap. Likewise, the right-side chart and slope conditions are
proved for the actual terminal; arbitrary externally supplied charts are
not covered by that transport. These distinctions are recorded below
and in the corresponding Blueprint Remarks.

| Original requirement | Current evidence | Verdict |
| --- | --- | --- |
| Integrate valid left/right work, including new files; retain old entry points | Integration manifest in `../build/core-integration/integrated-sources.json`; current imported modules; historical interface examples in `../scripts/core_contracts.lean` | Integrated and checked for the implemented scope |
| Upper bound, CWA and lower bound on the same family, shading and slope | `NormalizedContradiction.lean` passes `data.family`, `data.shading` and `data.analysisSlope` to the length-32 CWA lower theorem and compares it with `data.projection_upper`; the lower loss and cutoff precede the upper configuration | Proved |
| Rich Prop. 6.2 → reentrant Prop. 6.3 → actual C² construction | Required proof-value paths and upstream-binder checks in `../build/core-integration/core-proof-audit.json` | Proved |
| Relate the normalized terminal to the actual Node-6 output | `PaperTerminalNormalization.lean` retains source indices, exact tube/axis transport and shading containment; the final root reaches this construction | Proved |
| Lemma 6.6 in the actual left construction | The final root uses `pure_wz2_lemma66_prepared_interval`, with its mass, frame and cap supplied by the construction; the separately proved normalized-interval lemma derives its frame on any supplied C2 configuration | Constructed route proved; generic printed mass/cover extension remains a Remark |
| Correct the Lemma 7.12 density loss to η → 4η | `pure_wz2_lemma7_12_parameter_frostman_sharp_density`; checked parameter one-step proof-value chain | Proved in the explicit normalized parameter scope |
| Literal unit-capsule Prop. 7.1 in the literature comparison | `not_pureWZ2NormalizedOrdinaryTubeWolffProjectionStatement`, with a finite counterexample even for `f(z)=z` and a bounded vertical chart | Refuted literal model; recorded in `rem:longitudinal-tube-model` |
| Adopted Prop. 7.1 at general longitudinal positions | `DilatedTubeWolff.lean` and `DilatedTubeWolffLowerBound.lean`: coarse length 32, unchanged fine unit segments, parameter constant 128000, uniform cutoff and packing | Proved and used by the final root |
| Coordinate and slope normalization | `PaperTerminalNormalization.lean` proves the bounded base, vertical chart, shading window and centered nonsingular slope on the actual transported terminal, with quantitative losses | Proved for the configuration needed by the goal |
| CWA ⇒ Tube Wolff ⇒ Prop. 7.1 ⇒ Prop. 6.8 | `pure_wz2_convex_wolff_lower_bound_via_dilated_tubes` applies CWA to convex length-32 capsules and invokes the independent corrected Prop. 7.1; no common-height premise or extra cardinality assumption | Proved and used by the final root |
| Preserve `PureWZ2Theorem5_2Unconditional` with its original statement and no external proof inputs | Current theorem declaration and executable historical contract | Proved and checked |
| Update blueprint and compiled dependency data faithfully | Matching blueprint/docbuild imports; regenerated declaration registry, dependency data and 102 atlas correspondences | Done, with incomplete paper scopes identified |
| No placeholders, new axioms, circular final-theorem calls or dummy dependencies | 105 transitive axiom checks, 53 upstream-binder checks, 128 required value paths, 105 forbidden paths and 5 changed-source scans since the committed checkpoint | Passed |
| Required builds and `python3 blueprint/scripts/check.py --lean` | `blueprint/build/lake-build.log`: 9125 jobs, success; `check-blueprint-right-final.log`: 43861 project declarations and 187/298 linked declarations reached; `check-core-proof-right-final.log`: passed | Passed |

All twelve selected Core primaries occur in the final theorem's compiled
proof-value closure: Prop. 6.2, Prop. 6.3, Prop. 6.4, prepared Lemma 6.6,
Prop. 6.5, normalized Lemma 6.7, JetCount, the normalized cinematic
Thm. 7.13 input, sharp-density Lemma 7.12, corrected Prop. 7.1,
normalized Prop. 6.8 and the final contradiction.
The common-height and full-line alternatives are checked in separate
closures with the same Blueprint import inventory and strict agreement
of shared declaration records.

## Literature differences retained in Remarks

The accepted scope now includes both slope normalization and the explicit
coarse-tube correction. It does not assert equivalence of the corrected
test with the paper's literal unit-length capsule interpretation.

The current source defines
`PureWZ2NormalizedOrdinaryTubeWolffProjectionStatement` with:

- a uniform `eta` and scale cutoff chosen before the family and slope;
- nonempty, essentially distinct ordinary unit-segment tubes in the unit ball;
- the bounded vertical chart and ordinary unit-segment actual-volume Tube
  Wolff tests;
- dense shading in the slope window and a nonsingular slope with `f(0)=0`.

Lean proves the negation of this statement, using fixed `f(z)=z`, at
`epsilon=1/4`. Its axiom check uses only `propext`, `Classical.choice`
and `Quot.sound`. The counterexample already satisfies the chart
condition, so slope centering and general chart normalization cannot
repair this literal model.

The adopted repair is
`pure_wz2_proposition7_1_dilated_tube_wolff`: retain the given fine unit
segments and use finite coarse capsules of length 32. CWA supplies those
coarse tests directly. Both its normalized and unit-ball CWA endpoints are
compiled and audited. The normalized endpoint now supplies the final
lower bound. It is not an unproved implication from the original
unit-length tests, and it adds no hypothesis to the final theorem.

The standalone printed Lemma 6.6 from absolute slab mass and cover alone
remains unproved; its exact extra normalized mass and fine-cap requirements
are recorded in `rem:lemma66-mass-normalization` and the integration report.
For Prop. 7.1/6.8, arbitrary externally supplied charts and the
identification with every intended paper convention also remain outside
the adopted normalized theorem. These are documented literature gaps,
not missing inputs to the constructed final contradiction.

No CWA counterexample or failure of the already-compiled final theorem is
claimed. See [the integration report](core-proof-integration.md) for the
implemented mathematical connections and exact remaining hypotheses.
