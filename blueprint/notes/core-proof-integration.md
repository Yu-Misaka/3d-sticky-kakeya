# Core proof integration, 2026-10-30

This is a partial mathematical alignment with a compiled normalized final
contradiction. The actual Proposition 6.5 terminal is transported into one
normalized configuration, retaining its common-height unit segments.
The final CWA lower bound uses the **ordinary capsule** Tube Wolff theorem
with actual-volume tests. The complete paper Core DAG is **not** proved:
general Lemma 6.6 preparation remains open, and the ordinary-tube model
for arbitrary longitudinal positions needs a scope correction beyond the
proved terminal specialization. The literal normalized ordinary-capsule
claim is now refuted by a finite grid with fixed slope `f(z)=z`.
A concrete finite-capsule correction is also proved: coarse axes have
length 32, and every fine unit segment keeps its arbitrary longitudinal
position. CWA supplies these corrected tests directly. The resulting
projection theorem still uses a bounded vertical chart; its identification
with the intended paper convention is not silently assumed.
The user has accepted the slope-offset
difference as an explicit Remark: the roadmap uses the normalized
Proposition 7.1/6.8 interfaces, and the actual left-terminal transport proves
their applicability. Thus removing the slope-zero condition for arbitrary
supplied slopes is not a remaining requirement for the adopted route.
The kernel-checked arbitrary-offset counterexample records why this scope
correction is necessary; it is kept separate from the final proof.

The requirement-by-requirement [completion audit](core-goal-completion-audit.md)
separates verified implementation from full paper scope. The literal
unit-length Tube Wolff claim remains refuted after the accepted slope
normalization; adopting the compiled length-32 repair is a separate model
decision. Neither that decision nor this audit discharges generic Lemma 6.6
or the remaining chart transport.

The current left-focused work removes the frame prerequisite from the
normalized Lemma 6.6 for **every supplied configuration and interval**.
It keeps the previous normalized mass, cover and fine-cap hypotheses
exactly. The every-interval C2 source now calls this theorem after
constructing only a global cap. The remaining left gap is deriving that
normalized mass and cap from the printed absolute-mass hypotheses.

## Integrated work and the compatible terminal

The main checkout and both delivery checkouts started at
`a9b92a439e3a228bdef19b22f7c0e9eb36ca8866`; the main checkout was clean.
The integration copied 36 changed source/document files, including all nine
previously untracked Lean modules. Generated audit JSON and the generated
correspondence chapter were excluded and regenerated after integration.
The actual copied paths and hashes are recorded in
`blueprint/build/core-integration/integrated-sources.json`.

`PureWZ2NormalizedProjectionData sigma a delta` extends the unchanged
preparation record with `ConvexWolffBound` on its literal `family`. It contains
one ordinary family, shading and slope, with CWA error `delta^(-a)`, density
`delta^a`, base norms at most 4, analytic essential distinctness, vertical
chart, the height window, `f(0)=0`, nonsingularity, and upper bound
`volume (twistedUnion shading f) <= delta^(sigma-a)`.

`pure_wz2_node7_analytic_cleanup_with_cwa` constructs that record. Its CWA
proof normalizes the **same cleanup family's** absolute convex density by
its cardinality floor. The previously available parameter absorption bound
has factor 4800, whereas `deltaTubeVolume 1 <= 12`; it therefore already
pays for the required CWA normalization. No new power loss or additional
configuration is introduced. The proof handles arbitrary convex sets,
including sets of zero or infinite volume.

`PureWZ2NormalizedProjectionRefinement` retains the injective source-index
map, equality of each selected tube with its source, containment of each
selected shading, and the slope identity. The old cleanup, cutoff and
preparation interfaces are projections of this construction.

`PureWZ2CommonHeightProjectionData` additionally retains
`HasCommonHeightTubeModel` on the same family. The actual unit segments,
including their longitudinal positions, are canonical positive-vertical
segments centered at one `m` with `|m| <= 1`. This is proved from the exact
retubed representatives and their preservation through cleanup. The older
normalized record and statement follow by forgetting this witness, with
no new configuration choice.

The root `PureWZ2Theorem5_2Unconditional` retains exactly
`PureWZ2Theorem5_2Statement` and has no external proof arguments. It now uses
`CommonHeightContradiction`: choose the independent common-height CWA lower bound
at `epsilon = sigma/4`, obtaining `eta <= sigma/4` and its scale threshold;
then ask the left producer for **one** terminal at that `eta` below that
threshold. The lower bound and upper bound both refer to
`twistedUnion data.shading data.analysisSlope`. Since
`sigma/4 < sigma-eta`, their inequalities contradict `0 < delta < 1`.
The lower bound obtains ordinary capsule actual-volume Tube Wolff from
CWA, derives parameter counting by containment of the common-height
segments in an ordinary coarse capsule, and derives its polynomial
cardinality budget from packing. The old `NormalizedContradiction` API
remains available separately.

## Transport of the actual Node-6 terminal

`pure_wz2_node7b_common_height_from_retained_large_slope` uses
`node6.toLargeSlopeConfiguration`: its family is literally
`requested.finalTarget`, its shading is `requested.finalShading`, and its
slope is `safePublicSlope commonSource terminal`. The former call to
`pureWZ2_node7_affine_diagonal_preparation` has been removed from this proof.

For desired analytic loss `A`, request the paper output at `a=A/10000`.
The existing Node-6 schedule uses `epsilon=a/16000`. Before requesting the
source, `exists_actual_terminal_slope_offset_cutoff_for_output_loss` combines
the source-to-terminal radius bound
`terminalDelta <= sourceDelta^(1-2*epsilon)` with the existing bound
`1+|safePublicSlope(0)| <= K*sourceDelta^(-2*epsilon)`.
Since `2*epsilon < (1-2*epsilon)*a`, a uniform source cutoff gives
`1+|safePublicSlope(0)| <= terminalDelta^(-a)`.

For the actual slope `f`, put `s=f(0)` and `k=1/(4(1+|s|))`. The proved
linear equivalence is

```
A_s(x,y,z) = (k(x+s*y), k*y, z).
pi_(f-s)(A_s(p)) = (k*pi_f(p)_1, p_2).
```

`SlopeOffsetGeometry.lean` proves contraction, determinant `k^2`, exact
spatial volume transport and projected-area multiplier `k`.
`SlopeOffsetRetubing.lean` proves the exact supporting-line image. Source
line-class parameters become `|a'|,|b'| <= 1/12`, `|c'|,|d'| <= 1/2`.
Unit segments centered at a height `m` have bounded bases and the required
vertical chart. The image of the source paper body lies in the retubed
paper body. The image of its width-1/4 slab lies in the ordinary tube of
radius `12*terminalDelta`.

`SlopeOffsetNormalization.lean` selects that slab on the actual indexed
shading, retaining at least 1/12 of its mass. All indices are unchanged
before cleanup. It proves CWA transport with factor `k^(-2)` and density
transport whenever
`20736 * targetDensity <= k^2 * sourceDensity`.
The factor 20736 is 12 (slab) times 1728 (ordinary retubed mass compared
with the source radius-squared mass).

`exists_slopeOffset_normalization_budget` chooses its cutoff before `s`.
For `b=A/100=100a`, the scalar inequality
`3981312 * terminalDelta^b <= terminalDelta^(3a)` pays for both CWA and
density using the proved small-power offset bound. The upper bound
transports by `k<=1` and is weakened to the desired exponent at radius
`12*terminalDelta`. The analytic cleanup then supplies distinctness and
normalized CWA on one final configuration.

`PureWZ2PaperTerminalProjectionRefinement` retains an injective index map
to the actual source family, exact axis images, containment in the image
of each original slab shading, the source mass fraction, and slope equality
to `f.centered`. Its `projection_volume_le` theorem controls the final
projection by `k` times the original terminal projection. These are actual
geometric relations through the cleanup. The common source is used only
for the numerical bound on the same public slope.
The refinement also retains `tube_eq_model`, proving the exact unit-segment
identity used by its `common_height` theorem. The earlier
`pure_wz2_node7b_normalized_from_retained_large_slope` is the projection of
this stronger result, preserving its historical type.

## Mathematical connections verified in the implemented scope

| Connection | Actual mathematical data consumed |
| --- | --- |
| Prop. 6.2 to Prop. 6.3 | The rich kernel chooses the actual outer/inner M9 schedules and both sticky terminals; coarse re-entry is retained. |
| Prop. 6.3 to Prop. 6.4 | The C2 hierarchy receives the actual `PureWZ2ReentrantGrainSource` after fixing its losses and cutoff. The old AD bridge alone is not used as evidence of this connection. |
| Prop. 6.4 to a source for every later prescribed interval | Actual reentrant C2 output and certified Prop. 6.2 preconditioning supply one configuration with a global fine cap before the interval. The normalized lemma now constructs its frame on each supplied slab. |
| Prescribed slab to prepared Lemma 6.6 | The whole-cell hull preserves slab mass and transfers its cover and incidence cap. The mass hypothesis remains explicitly normalized by `delta^2 * #family`. |
| Any supplied normalized slab to its frame certificate | Finite short-grain counting and mass selection retain half the slab mass on the original family. Local AD and the tube-segment direction estimate give the projected-normal lower bound. No new configuration is selected. |
| Prepared Lemma 6.6 to the Prop. 6.5 construction | The derivative bound is proved on the chosen slab and slope, with convex overload proved inside the lemma. Prop. 6.5 supplies the extra preparation, and now consumes the strengthened global-cap C2 source. |
| Actual Prop. 6.5 terminal to normalized Lemma 6.7 | The returned paper family, shading, slope, CWA and upper bound enter the explicit affine/slab/retubing/cleanup transport. |
| Curve/JetCount and corrected Thm. 7.13 to parameter Lemma 7.12 | The representative cinematic pullback, Katz–Tao count and PYZ estimate are actual inputs of the complete one-step proof. |
| Parameter Lemma 7.12 to parameter Prop. 7.1 | The completed one-step theorem is used by finite GridOS scheduling, coarsening, termination and telescoping. |
| Ordinary Tube Wolff to parameter Prop. 7.1 on the actual model | Common-height parameter clusters are contained in ordinary radius-`8r` coarse capsules. Radius-squared tests give `64 C`, and actual-volume tests give `640 C`. |
| Physical full-line Tube Wolff to parameter Prop. 7.1, retained API | Parameter clusters are contained in radius-`20r` full-line tests; the volume bound gives Frostman constant `172800 C`. |
| Ordinary capsule radius-squared to actual-volume tests | Exact capsule volume proves the forward implication for every positive radius with constant `C`, and the converse with `10 C`. This does not identify capsules with full-line tests. |
| CWA to ordinary Tube Wolff to normalized Prop. 6.8 | CWA supplies ordinary actual-volume tube tests. The final lower bound calls the ordinary-tube Proposition 7.1 and packing supplies `D=7`. The common-height model and chart are proved by the actual terminal construction. |
| Normalized upper and lower bounds to contradiction | CWA, all normalization conditions and the upper bound belong to one cleanup configuration. |

The table distinguishes the prepared and normalized statements from the
paper's general scope. The original unit-segment coarse-test predicate
has not been identified with the full-line predicate.

## Ordinary Tube Wolff on the actual common-height terminal

`CommonHeightTubeWolff.lean` proves a direct ordinary-capsule reduction.
When the four line parameters differ by at most `r` and `|m| <= 1`, the
centers `(a+c*m,b+d*m,m)` differ by at most `4*r`. Normalization on vectors
of norm at least one gives unit-direction distance at most `2*r`.
Corresponding points of the centered unit segments differ by at most
`5*r`. Therefore, for `delta <= r`, the complete fine capsules lie in
one ordinary coarse capsule of radius `8*r`. This proves indexed
parameter Frostman with constant `64*C` from ordinary radius-squared
Tube Wolff. For `8*r > 1`, total cardinality gives the required bound.
All indices are retained in this count.

`OrdinaryTubeWolffLowerBound.lean` uses the exact-volume conversion,
giving factor `640*C` for the paper's ordinary-volume tests at every
positive radius. `pure_wz2_proposition7_1_ordinary_tube_wolff` absorbs
this constant in half of the parameter theorem's source loss, with all
cutoffs chosen before the runtime family, common center and slope.
It calls the full parameter one-step/GridOS/telescoping engine.
Packing removes its polynomial cardinality budget for analytic
distinctness; `pure_wz2_ordinary_tube_wolff_lower_bound_in_unit_ball`
uses the paper's ordinary centered-dilation distinctness instead.

`ordinaryTubeWolffVolumeBound_of_convexWolffBound` applies CWA to each
convex ordinary capsule. The normalization factor `deltaTubeVolume 1 >= 1`
gives the actual-volume count with the same constant. Consequently
`pure_wz2_convex_wolff_lower_bound_in_common_height_chart` follows
`CWA -> ordinary capsule Tube Wolff -> ordinary Proposition 7.1`.
`CommonHeightContradiction` evaluates it on exactly the family, shading
and slope produced by `pure_wz2_left_line_common_height_projection`.

The common-height property is proved upstream by
`PureWZ2PaperTerminalProjectionRefinement.common_height`; it is not an
extra hypothesis of the final theorem. No new density, CWA or volume loss
is needed to retain it. The final proof-value audit excludes both the
old full-line projection theorem and the direct CWA-to-parameter shortcut.
The ordinary projection theorem itself has no CWA or left-line input.

## Physical full-line Tube Wolff route, retained interface

`FullLineTubeWolffBound F R C` tests the actual sets
`cthickening r (tubeAxisLine T) ∩ closedBall 0 R`, for `delta <= r <= 1`,
and counts containment of the given ordinary fine carriers, including all
their indices. It does not mention line parameters. This predicate is
different from the unchanged `TubeWolffBound`, whose coarse tests are
unit-segment capsules.

For bounded bases and a vertical chart, the radius-r parameter cluster is
contained in the radius-20r physical full-line test in `B(0,6)`. The test
volume is at most `432*(20r)^2 = 172800*r^2`. For `r>1/20`, the total
cardinality bound gives the same conclusion. This proves
`tubeParameterFrostmanBound_of_fullLineTubeWolffBound` without any CWA
premise. `pure_wz2_proposition7_1_full_line_tube_wolff` then calls the
existing full one-step/GridOS/telescoping engine, for each polynomial
cardinality exponent `D>0` chosen before epsilon and the scale cutoff.

Both `pure_wz2_convex_wolff_lower_bound_in_vertical_chart` and the original unit-ball
variant still use CWA to supply the full-line tests and invoke this theorem.
The former derives `D=7` from analytic distinctness; the latter uses
ordinary paper distinctness for the packing bound. Their public statements
are unchanged. Neither proof uses the older direct CWA-to-parameter theorem.
The full-line theorem itself is independent of CWA and the left upper bound.
These interfaces retain their old statements, which do not impose common
center heights. They are no longer the lower-bound path of the final root.

`OrdinaryTubeWolff.lean` separately proves the equivalence, up to fixed
constants, between the repository's radius-squared ordinary capsule tests
and the paper's actual-volume tests at every positive radius. The exact
capsule volume is `pi*r^2 + (4/3)*pi*r^3`. A coarse capsule of radius below
`delta` cannot contain a fine capsule, by strict volume monotonicity.
Radii above one are controlled by the total cardinality. Thus
`TubeWolffBound.to_ordinaryVolume` retains `C >= 1`, and
`OrdinaryTubeWolffVolumeBound.to_radiusSquared` loses only a factor `10`.
No full-line or chart conversion is claimed in these lemmas.

## Lemma 7.12 density repair

The complete normalized theorem
`pure_wz2_lemma7_12_parameter_frostman_sharp_density` has source density
`delta^eta` and output density `delta^(4*eta)`, with the same radius and
neighborhood comparison conclusions.

The improvement is in the actual OS construction. The planar grid is chosen
using `eta/2`, so its atomization-plus-OS loss is at most `delta^(-eta)`.
The multiplicity-band loss is at most `delta^(-eta)`. Their product is at
most `delta^(-2*eta)`, giving density `delta^(3*eta)` on the same retained
shading. This stronger estimate is passed through projection uniformization
and the positive-window theorem, including their actual witness data.

For the signed theorem, use `positiveEta = 4*eta/3`. The gap `eta/3` pays for
the factor 1/2 in selecting a half-window; `3*positiveEta = 4*eta` gives the
claimed density. The new maximum admissible source loss is three quarters
of the positive-window maximum. All these choices, including the grid base
and reflection/absorption cutoff, precede the runtime family and slope.
The previous `eta/2 -> 4*eta` API follows by weakening the input, and remains
the API consumed by the unchanged finite-iteration schedule.

This fixes the density issue for the **parameter** theorem. It does not
remove its vertical-chart, parameter-Frostman or slope-zero hypotheses.

## Prepared Lemma 6.6 over the entire interval-length range

`pure_wz2_lemma66_prepared_interval` fixes
`0 < sigma < 1`, `0 < epsilon <= 1/2`, `eta > 0`, and
`1000*eta <= epsilon*sigma^2`, then chooses a single cutoff. It works for
every later `delta` and prepared interval with
`delta^(1/2) <= rho <= delta^epsilon`.

Its input `PureWZ2Lemma66PreparedInterval sigma eta delta` contains:

- a C2 grain configuration of loss `eta/8`;
- the same globally C2 slope representative, with `|f|, |f'|, |f''| <= 1`
  on `[-1,1]`;
- a whole-cell subshading on an interval of width `rho` in `[-1,1]`;
- mass at least `(pi/4)*delta^(eta/8+2)*#family*rho` and a cover by at most
  `delta^(-eta/8)*rho^(-2+sigma)` balls of radius `rho`;
- the point-multiplicity bound `(delta/rho)^(2-sigma-eta/8)*#family`;
- the additional cap
  `delta^(2-sigma-eta/4096)*rho^(-eta/4096)*#family`;
- frame-normal compatibility: when the source slope is within `1/50` of
  the chosen frame slope, the projected local normal has norm at least `1/16`.

There is no derivative lower-bound hypothesis, convex-overload input, or
critical-package argument in this lemma. Internally it writes
`rho = delta^p`, proves `epsilon <= p <= 1/2`, uses the worst endpoint for
the scalar cutoff, and applies the existing common-slice/prism/AD argument.
The old power-scale theorem is now a specialization of this uniform theorem.

## Prescribed slabs and a C2 source chosen before every interval

`PrescribedSlabHull.lean` resolves the whole-cell preparation for an arbitrary
prescribed slab `J=[a,b]`: retain all occupied `delta`-cells that intersect
the slab. Every original slab incidence is retained, so indexed mass does
not decrease. For each retained point `p`, the proof supplies a point `q`
in the original slab at distance at most `2*delta` and height difference
at most `delta`, with exactly the same tube-incidence predicates. Hence
the original cover works at radius `r+2*delta`, and any multiplicity cap
within the original slab transfers to the entire hull. A padded interval
of width `r+2*delta` can be placed inside `[-1,1]`, containing `J` and the
hull. No different height layer is selected.

`pure_wz2_lemma66_prescribed_interval` uses that hull and the prepared
theorem at `epsilon/2`, with a cutoff chosen before the configuration and
interval. It assumes `2000*eta <= epsilon*sigma^2` and:

- a C2 configuration of loss `eta/8`, frame compatibility and its
  normalized global slope;
- `sqrt(delta) <= r=|J| <= delta^epsilon`;
- slab mass at least `(pi/4)*delta^(eta/16+2)*#family*r`;
- a cover by at most `delta^(-eta/16)*r^(-2+sigma)` balls of radius `r`;
- one slab cap `mu(p) <= delta^(2-sigma-eta/8192)*#family`.

It concludes `r <= |f'(z)|` throughout `J`. Since `r+2*delta <= 3*r`,
uniform cutoffs absorb factors `3` in mass and interval width, and `9`
in covering. The single cap supplies both prepared multiplicity bounds.

`pureWZ2_c2_source_with_fine_cap` now constructs a C2 source with any
requested positive cap loss. It uses the actual C2 producer and the
certified Prop. 6.2 preconditioning, then weakens its loss. The actual
Node-6 fixed-scale assembly consumes this producer and weakens its global
cap to the historical power-scale interface. This is a real dependency
of the final theorem, with its old API unchanged.

`pureWZ2_interval_ready_c2_source` still provides the stronger historical
source with a global cap and frame certificate. Its statement is unchanged
and its proof is audited independently.

## Frame preparation for an arbitrary supplied configuration

`pure_wz2_lemma66_normalized_interval` has the same mass, cover, scale and
multiplicity hypotheses as `pure_wz2_lemma66_prescribed_interval`, but no
frame prerequisite. In particular the supplied configuration is arbitrary,
the cutoff precedes both that configuration and `J`, and the proof does not
call a C2 source producer or a downstream theorem.

The construction is explicit:

1. The existing occupied-cell hull preserves the prescribed slab mass.
2. `ShortGrainCells.lean` partitions its fine cells by their global-grain
   label and a bin of width `sqrt(delta)` along the grain's rotated y-axis.
   The number of packets is at most
   `(R/delta+2) * 24*delta^(-loss)*(1/delta)^(1-sigma) * 6/sqrt(delta)`.
3. `DenseCellRefinement.lean` uses actual indexed mass and the fine cap
   to retain packets of volume at least
   `144*delta^(eta/2)*delta^2*sqrt(delta)`. The retained shading has at
   least half the hull's mass and consists of whole original cells.
4. Each packet lies in a radius-`6delta`, length-`4sqrt(delta)` tube
   segment and a radius-`4sqrt(delta)` ball about any of its points.
   `DenseGrainNormal.lean` applies local AD at scale `16delta` and the
   proved tube-segment direction lemma. The local normal has small inner
   product with the packet's long axis, so its projection in each required
   nearby frame has norm at least `1/2`.
5. `SlabFramePreparation.lean` assembles that certificate on the retained
   shading of the **same family**. Intermediate mass loss `3*eta/32`
   absorbs the hull enlargement and the factor two refinement loss.
   The prepared interval core now requires frame control only on that
   retained slab. The original global-frame interfaces remain available.

The closed `pure_wz2_left_line_c2_prescribed_intervals` now uses
`pureWZ2_c2_source_with_fine_cap` directly, before **any** later `J`.
It then calls the new arbitrary-configuration lemma on that same source.
Its statement is unchanged. It no longer invokes the square-root frame
producer. Its caller supplies no whole-cell, frame or multiplicity data.
This source API and the historical frame APIs have their own compiled
closures; no dummy references are inserted into the final proof.

## Remaining requirements

1. **Printed Lemma 6.6 from its absolute mass and cover.** The new theorem
   accepts arbitrary supplied configurations and constructs the slab
   frame, but still needs mass
   `(pi/4)*delta^(eta/16+2)*#family*|J|` and cap
   `delta^(2-sigma-eta/8192)*#family` on the supplied slab.
   The printed mass is `delta^eta*|J|`. No cardinality ceiling controlling
   `delta^2*#family` is available; CWA supplies a floor. Nor is the cap
   obtained merely by selecting a dyadic multiplicity band.
   A remaining preparation lemma must retain enough of this **prescribed**
   slab to supply both quantitative bounds, or prove the derivative
   conclusion directly. Global refinements and the constructed-source
   theorem do not establish that retention for an arbitrary input slab.
   This is recorded in `rem:lemma66-mass-normalization`, without asserting
   the printed lemma false or treating it as an accepted scope correction.

2. **Arbitrarily supplied ordinary tubes and charts.** `TubeWolffBound` tests
   containment of complete unit-segment capsules in coarse unit-segment
   capsules. The four-parameter map forgets longitudinal base position.
   For the actual terminal, the proved common-height property now gives
   parameter-cluster containment in a single ordinary coarse capsule and
   the final contradiction uses that ordinary-tube theorem. For an
   arbitrary supplied family, the four line parameters alone still do not
   locate the unit segments longitudinally. The paper defines
   unit-segment tubes in Section 2.1 (page 6 of the pinned v2), invokes the
   line-parameter identification in Remark 7.4 (page 40), and uses cropped
   full-line carriers after refinement/rotation in the proof of Lemma 7.12
   (page 43). A general quantitative model reduction would have to preserve
   enough shading mass, the appropriate indexed count, projected-area
   comparison and uniform quantifier order. The new longitudinal grid
   shows that this cannot follow from the literal ordinary unit-segment
   tests alone, even with `f(z)=z` and a bounded vertical chart. Its proof
   is recorded below. The new finite-capsule theorem provides a concrete
   change of coarse tests: length 32 instead of length 1. Its geometric
   parameter reduction works for arbitrary longitudinal positions, and
   CWA supplies its stronger tests. Identifying that model with the intended
   paper convention and extending the chart transport remain separate
   unresolved scope requirements, not accepted normalization corrections.
   Both the actual common-height ordinary-tube specialization and the earlier
   full-line specialization remain proved. The original final theorem is
   not used in either counterexample or to make a generic intermediate
   statement vacuous.

## Scope note accepted for the roadmap

The slope-offset caveat is recorded in `rem:parameter-frostman` and in the
Prop. 7.1/6.8 atlas correspondences. It is an adopted normalization
correction, not a reason to stop alignment. The mathematical requirement
is the already-proved transport of the actual left terminal into the
same normalized configuration used for both projection bounds. This
acceptance does not replace any missing proof of the arbitrary-interval
Lemma 6.6 or of tube/chart reductions for an arbitrary supplied family.
The actual common-height terminal now has its own proved ordinary-capsule
specialization, as described above.

**Full paper Prop. 6.8 scope.** The normalized specialization now does
   follow `CWA -> ordinary capsule Tube Wolff -> common-height Prop. 7.1`.
   The unrestricted CWA statement remains open. It cannot be obtained
   through the refuted unrestricted Tube-Wolff-only claim. Extending the
   adopted result to that unrestricted scope would need either
   an argument using the stronger CWA condition or a justified correction
   with proved normalization. The original final theorem is never used
   to prove either side or any intermediate lemma.

## Verified obstruction to arbitrary slope offsets in Proposition 7.1

`SlopeOffsetCounterexample.lean` proves
`not_pureWZ2UnrestrictedTubeWolffProjectionStatement`. The negated statement
chooses `eta > 0` and a scale cutoff **before** the family, shading and slope,
and asks for a uniform projection lower bound under ordinary capsule Tube
Wolff, unit-ball containment, paper essential distinctness and nonsingularity.
For every proposed `eta` and cutoff, the construction gives a counterexample
at `epsilon = 1/4`. No final Kakeya theorem or CWA lower bound is used.

For an integer `n > 0`, set `delta = 1/(4096*n)`, mesh `1/(64*n)` and
`s = 1/sqrt(delta)`. The `n*n` lines are

```
x = a + c*z,       y = -(a + c*z)/s,
a = i/(64*n),     c = j/(64*n),     0 <= i,j < n.
```

The actual ordinary unit segments are centered at height zero, and the
shadings are their complete radius-`delta` capsules. The following are proved:

- `planarTubeGrid_in_unitBall`: the full capsules lie in the unit ball.
- `planarTubeGrid_ordinary_distinct`: neither capsule is contained in the
  centered double of another. Containment would force `|a-a'| <= 3*delta`
  and `|c-c'| <= 48*delta`, below the mesh `64*delta`.
- `planarTubeGrid_parameter_frostman`: two grid-coordinate counts give
  parameter Frostman constant `150994944`, independent of `s`.
- `tubeParameterFrostman_to_centered_tubeWolff`: for segments covering heights
  `0` and `1/8`, containment in an arbitrary coarse ordinary capsule forces
  a parameter cluster of radius `160*r`. This gives capsule Tube Wolff
  constant `25600*C`, so the grid constant is `3865470566400`.
- `offsetObstruction_projection_volume_le`: the axes lie in `x+s*y=0`,
  and the actual shaded twisted area for `f(z)=s+z` is at most
  `12*s*delta+20/s = 32*sqrt(delta)`. The slope is globally C2 with
  `f'=1` and `f''=0`.
- `exists_planarTubeGrid_slope_offset_counterexample`: select `n` large
  enough that `delta` is below the proposed cutoff, the fixed Tube Wolff
  constant is at most `delta^(-eta)`, and
  `32*sqrt(delta) <= delta^(3/8) < delta^(1/4)`. Full shading supplies the
  required `delta^eta` density. The same grid has the bounded vertical chart.

The pinned v2 prints Proposition 7.1 on page 39 with a cutoff uniform over
the later slope and no bound on `f(0)`. Its Section 2.1 definitions use
ordinary unit-segment neighborhoods and the centered-dilation distinctness
verified here. The repository statement uses the normalized radius-squared
Tube Wolff count. This is stronger, on `delta <= r <= 1`, than the printed
volume count, up to an absolute constant.

This construction asserts **no CWA certificate**. It does not refute the
CWA-only Proposition 6.8 or the compiled normalized final contradiction.
The actual left terminal has the previously proved small-power offset
bound, and its existing normalization remains valid. The counterexample
is kept outside the final-root dependency closure and checked separately.

## Verified longitudinal obstruction with fixed normalized slope

`LongitudinalTubeWolffObstruction.lean` proves
`not_pureWZ2NormalizedOrdinaryTubeWolffProjectionStatement`.
This is independent of the accepted slope-offset caveat: the slope is
always `f(z)=z`. The claim being negated permits arbitrary longitudinal
positions of the fine unit segments and tests complete capsule containment
in coarse capsules of the same unit length. It uses the actual-volume
Tube Wolff tests at **every positive radius**.

For `n>0`, set `delta=1/(4096*n^2)`, `mu=1/(64*n^2)=64*delta`, and
`w=1/(64*n)=sqrt(delta)`. Use the `n^5` lines

```
x = mu*i + mu*j*z,
y = mu*k - mu*j + mu*l*z,
0 <= i,k,l < n,  0 <= j < n^2,
unit-segment center height = w*i.
```

The seven new modules prove the geometry, distinctness, count and scale
selection in separate steps:

- `ordinary_capsule_midpoint_dist_of_subset`: the midpoint of a fine
  unit-segment capsule contained in a coarse radius-`r` unit-segment capsule
  lies within `2*r` of the coarse midpoint. Two contained tubes therefore
  have center heights differing by at most `4*r`.
- `ordinary_capsule_pair_parameter_bounds`: if both segments cover
  heights `[-1/8,1/8]`, coarse containment for `r<=1/8` forces every line
  parameter difference to be at most `160*r`.
- `longitudinalTubeGrid_in_unitBall` and
  `longitudinalTubeGrid_ordinary_distinct`: the full capsules lie in
  `B(0,1)` and satisfy the literal centered-dilation distinctness condition.
  Their four line parameters lie in the bounded vertical chart.
- `longitudinalTubeGrid_tubeWolff`: the center-index count is at most
  `1+512*r*n`. Each of the other three coordinate counts is at most
  `65536*r*n^2`, and the `k,l` counts are also at most `n`. Splitting at
  `r*n=1` yields the absolute radius-squared Tube Wolff constant `2^60`.
  The proved ordinary-volume conversion supplies every positive coarse
  radius, including radii outside `[delta,1]`.
- `longitudinalTubeGrid_projection_volume`: the axis projection for
  `f(z)=z` is `mu*i + mu*k*z + mu*l*z^2`; the entire full-shading
  projection has area at most `24*w=24*sqrt(delta)`.
- The final construction chooses `n` after the proposed `eta` and cutoff,
  absorbs `2^60` into `delta^(-eta)`, and makes
  `24*sqrt(delta) <= delta^(3/8) < delta^(1/4)`. Full shading supplies
  the required `delta^eta` density.

The new root and its transitive axiom set have compiled; the axiom set is
exactly within `propext`, `Classical.choice`, `Quot.sound`. It is included
in a separate supplemental proof-value closure. The audit checks that
neither counterexample is used by the final root, the ordinary/full-line
projection theorems or the actual common-height terminal, and that the
new negation uses no final theorem or CWA projection bound.

No CWA certificate is asserted for this example. The actual terminal
has the common-height property proved by its construction and its final
contradiction is unaffected. The blueprint records the new result in
`thm:twisted-longitudinal-obstruction` and `rem:longitudinal-tube-model`.
It refutes the literal broad ordinary-capsule claim, not the main Kakeya
theorem, the CWA-only claim, or every intended convention for the paper's
tubes. The outstanding paper-model requirement remains explicit.

## Finite coarse capsules at arbitrary longitudinal positions

`DilatedTubeWolff.lean` and `DilatedTubeWolffLowerBound.lean` give a
positive model correction. The coarse tests are centered dilations by
32 of ordinary radius-`r/32` tubes: finite capsules of radius `r` and
axis length 32. The given fine capsules still have unit-length axes;
their indices, longitudinal positions and shadings are unchanged.

`DilatedTubeWolffVolumeBound F 1 C` is proved equivalent to the old
`OrdinaryTubeWolffVolumeBound F C`. The result at factor 32 is explicitly
a different coarse-test premise. No implication from factor 1 to factor 32
is claimed. Both body CWA and the normalized ordinary-carrier CWA supply
the factor-32 tests directly, since these capsules are convex affine images
of ordinary capsules.

The geometric reduction works for any fine family with base norms at
most 4 in the vertical chart:

- For a reference line with base norm at most 4, its radius-`r`
  neighborhood in `B(0,6)`, with `0<r<=1`, fits in the length-32 capsule
  at the same radius. A nearest point on that line has norm at most 7,
  so its axis parameter relative to the reference base is at most 11
  in absolute value. This leaves room at both ends of the coarse axis.
- A parameter cluster of radius `r` lies in this coarse capsule at radius
  `20*r`. Its volume is at most `320*(20*r)^2=128000*r^2`.
  Larger `r` use total cardinality. Hence
  `tubeParameterFrostmanBound_of_dilatedTubeWolffBound` gives the indexed
  Frostman constant `128000*C`, without common-height or CWA premises.
- `pure_wz2_proposition7_1_dilated_tube_wolff` absorbs the constant before
  the family and its segment positions are supplied, then uses the complete
  parameter one-step/GridOS/telescoping proof. Its only count assumption
  is the physical finite-capsule count. Packing removes the polynomial
  cardinality premise for analytic distinctness, or for ordinary paper
  distinctness in the unit ball.
- `pure_wz2_convex_wolff_lower_bound_via_dilated_tubes` and the unit-ball
  variant follow `CWA -> length-32 capsule tests -> corrected Proposition
  7.1 -> parameter iteration` on the given fine family, shading and slope.
  They assume no common-height model or separate Tube Wolff certificate.

These endpoints do not use the full-line projection theorem, the direct
CWA-to-parameter shortcut, a final theorem or either counterexample.
The audit checks their proof-value paths in independent supplemental
closures. The original final root continues to use its proved common-height
ordinary unit-capsule specialization, with its unchanged statement.

The new result supplies a concrete positive correction for the longitudinal
issue. It is not presented as proof of the refuted unit-length statement,
nor as completion of arbitrary-chart transport or printed Lemma 6.6.
The blueprint records its exact hypotheses in `lem:dilated-tube-cluster`,
`thm:twisted-dilated` and `cor:twisted-cwa-dilated`.

## Reproduction and verification

Run from the main checkout:

```sh
lake build MyLeanRepo.Kakeya.Assouad.PureWZ2.LeftLine MyLeanRepo.Kakeya.Assouad.PureWZ2.PaperNormalizedProjectionLowerBound MyLeanRepo.Kakeya.Assouad.PureWZ2.Theorem5_2Unconditional MyLeanRepo.Kakeya.Assouad.PureWZ2.SlopeOffsetCounterexample MyLeanRepo.Kakeya.Assouad.PureWZ2.OrdinaryTubeWolffLowerBound MyLeanRepo.Kakeya.Assouad.PureWZ2.LongitudinalTubeWolffObstruction MyLeanRepo.Kakeya.Assouad.PureWZ2.DilatedTubeWolffLowerBound
python3 blueprint/scripts/atlas.py --remarks
python3 blueprint/scripts/check.py --lean
lake env lean blueprint/scripts/core_contracts.lean > blueprint/build/core-integration/core-contracts.log
python3 blueprint/scripts/check_core_proof.py
git diff --check
```

`core_contracts.lean` checks old public interfaces, the unchanged final
statement, 105 transitive axiom sets and 53 actual upstream-argument uses.
`check_core_proof.py` reads the kernel graph generated by the blueprint audit,
follows only proof/definition **value** edges, checks required and absent
paths, and scans changed Lean sources for proof placeholders and additional
axioms. Thirteen APIs are checked in supplementary kernel closures: the old
full-line unit-ball endpoint, the transport record's projected-volume
corollary, the offset counterexample, the prescribed-interval C2 source,
the forward ordinary-volume conversion, the old normalized contradiction,
the old normalized upper-bound entry, the new ordinary-tube unit-ball
endpoint, the normalized longitudinal obstruction, and the two new CWA
endpoints through finite length-32 coarse capsules, plus the historical global-frame prescribed-interval theorem and frame-ready C2 source. The new normalized interval lemma is reached through the closed every-interval source. The reverse ordinary
volume conversion is now used in the final root.
Shared records are checked for
identical dependency data and declaration metadata before merging them for
the audit. The supplementary driver uses exactly the blueprint import
inventory in the same order. This matters for independently compiled,
same-name helper theorems already in the repository: importing a smaller
module set can expose another proof of the same proposition. The audit
keeps its strict equality check and compares one consistent environment.
No reference
to these APIs is inserted into the final proof merely to make them reachable.
Its result separately lists both refuted claims and remaining paper-level gaps.
The full blueprint audit regenerates declaration and dependency data.
These checks certify the implemented scope, not completion of the remaining
missing mathematical requirements.

Validation for the implemented scope passed and is recorded in the generated logs and
`blueprint/build/core-integration/core-proof-audit.json`:

- Related left/right modules, both ordinary finite-capsule lower-bound
  routes, the unchanged final entry and both finite counterexamples:
  `lake build`, 9,125 jobs, exit 0 (`build-left-frame-core.log`).
- `python3 blueprint/scripts/check.py --lean`: 43,859 project declarations,
  186 of 298 linked declarations reached, 102 atlas correspondences and
  242 proposed edges compared; exit 0. The compiled audit data were regenerated.
- `core_contracts.lean`: all historical interfaces, 105 axiom checks and 53
  upstream-argument checks passed; all axiom sets are within
  `propext`, `Classical.choice`, `Quot.sound`.
- `check_core_proof.py`: 124 required proof-value paths, 95 absent paths,
  and 89 changed Lean source scans passed. The absence targets are checked
  as existing Lean constants; a misspelled target cannot pass silently.
- `git diff --check`: passed.

The absence audit explicitly confirms that neither the old full-line
projection theorem nor the direct CWA-to-parameter theorem lies in the
new final proof-value closure. It also checks that the ordinary Tube Wolff
theorem does not depend on the left upper bound or on a CWA supplier.
Both counterexamples are absent from the final and ordinary/full-line
projection proof closures. The new longitudinal negation uses neither
a final theorem nor either side of the final contradiction.
The length-32 coarse-test theorem is independent of CWA suppliers and
the earlier projection bounds. Its two CWA corollaries call it through
the proved finite-capsule tests, without the direct CWA-to-parameter
shortcut or the full-line projection theorem.

Current logs: `build-dilated-core.log`,
`check-blueprint-dilated.log`, `core-contracts.log`, and
`check-core-proof-dilated.log`, all under
`blueprint/build/core-integration/`. The atlas's contradiction primary
points to the actual common-height contradiction; the subsequent
static check is in `check-blueprint-dilated-static.log`.
The separate LSP axiom checks of both
`not_pureWZ2UnrestrictedTubeWolffProjectionStatement` and
`not_pureWZ2NormalizedOrdinaryTubeWolffProjectionStatement` returned only
the three standard axioms and no source-scan warnings.
The separate checks of
`tubeParameterFrostmanBound_of_dilatedTubeWolffBound` and
`pure_wz2_convex_wolff_lower_bound_in_unit_ball_via_dilated_tubes`
returned the same standard basis and no source-scan warnings.
