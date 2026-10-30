# Left-line construction interfaces

The module `MyLeanRepo.Kakeya.Assouad.PureWZ2.LeftLine` stops at the upper
bounds of Lemma 6.7.  It does not import the final contradiction target.
Existing public node types remain available.

The subsequent single-agent integration adds a normalized CWA terminal,
uniform prescribed-interval theorems, a C2 source with frame and global
multiplicity preparation before the interval, and final contradiction. See
[core-proof-integration.md](core-proof-integration.md) for the current
implemented scope, remaining paper-level gaps and verification results.

| Paper step | Construction interface | What the next step uses |
| --- | --- | --- |
| Proposition 6.2 | `pure_wz2_node03_rich_prop62_kernel` | Rich terminal schedules with exact normalization losses, degrees, balanced covers, and coarse re-entry; the old public kernel is projected from their terminal calls |
| Proposition 6.3 | `pure_wz2_node04_reentrant_grains` | One `PureWZ2ReentrantGrainSource`: grains, critical volume floor, chart bounds, ordinary/cropped re-entry and its axial margin on the same shading |
| Proposition 6.4 | `pureWZ2_c2_grains_from_reentrant` | Calls that producer after freezing the hierarchy and scale cutoffs, then feeds the returned source into `p7ActualJohnScaleCoversFromInitial` |
| C2 source for every later interval | `pure_wz2_left_line_c2_prescribed_intervals` | One actual configuration and slope with a global fine cap are chosen before every later interval. The normalized Lemma 6.6 now proves its frame after each interval is supplied |
| Lemma 6.6, prescribed-interval version | `pure_wz2_lemma66_prescribed_interval` | The occupied-cell hull preserves the original slab mass and transfers its cover and cap, then applies the uniform prepared theorem; mass is normalized by `delta^2 * #family` |
| Lemma 6.6, arbitrary supplied configuration with normalized mass | `pure_wz2_lemma66_normalized_interval` | The original family and slope are retained, and every selected shading is a proved subshading of the input. Short-grain selection retains half of the prescribed slab mass; local AD proves the slab frame. Only normalized mass and the fine multiplicity cap remain extra quantitative hypotheses |
| Lemma 6.6, prepared power-scale version | `pure_wz2_lemma66_prepared` | A derivative lower bound on the same prepared slab and slope; convex overload is proved inside this theorem |
| Proposition 6.5 | `pure_wz2_node06_large_slope_retained` | `PureWZ2LargeSlopeConstruction`, retaining the common-y source, terminal geometry, cleanup, source regularization, requested CWA selection and terminal certificate |
| Lemma 6.7 | `pure_wz2_node7_from_large_slope` | The actual large-slope configuration and its projection certificate |
| Normalized Lemma 6.7 | `pure_wz2_node7b_normalized_from_retained_large_slope` | The actual Node-6 paper family, shading, public slope, CWA and projection bound, with explicit affine/slab/cleanup transport |
| Common-height normalized Lemma 6.7 | `pure_wz2_left_line_common_height_projection` | The same terminal also retains exact common-height unit segments; this supplies the retained ordinary capsule lower bound; the final root uses the length-32 correction and needs only the normalized output |

The closed entries are `pure_wz2_left_line_lemma67` and
`pure_wz2_left_line_lemma67_preparation`.  Their only mathematical input is
the same positive critical package used in Section 6.  The first has arbitrary
positive output loss; the latter requires `0 < analyticLoss < sigma`.
Both use the blueprint correction `sigma - loss`.

## Qualifications for the Core proof DAG

1. The public Node-4 statement is now projected from the same reentrant
   producer consumed by Node 5.  Its old AD bridge alone still cannot recover
   a reentrant grain witness.  The strengthened type must therefore appear
   on the construction edge, not just the old existential statement.
2. `pure_wz2_node04_reentrant_grains_from_prop62` threads the strong Node-3
   kernel through the M9 outer and inner schedules and both sticky calls.
   The returned terminal witnesses supply the actual selected families.
   The older capability's normalization exponent is still used for re-entry
   bookkeeping, but is not the mathematical evidence for this edge.  The
   strengthened kernel also proves the old public `kernel` field through
   `PureWZ2RichProp62KernelStatement.toReentryKernel`.  Do not infer the rich
   output from the old, weaker capability type alone.
3. `pure_wz2_lemma66_prepared` is independent of a critical package and has
   no convex-overload or derivative hypothesis.  It takes a prepared slab
   with `rho = delta^epsilon`, exact shading, normalized slope, frame-normal
   compatibility and multiplicity control. This power-scale entry now
   specializes `pure_wz2_lemma66_prepared_interval`, whose cutoff is uniform
   for `sqrt(delta) <= rho <= delta^epsilon`. The prescribed-interval hull
   now removes the whole-cell input. A strengthened actual C2 source
   supplies frame compatibility and a global cap before every later `J`.
   Its slab mass hypothesis is still `(pi/4)*delta^(eta/16+2)*#family*|J|`;
   no cardinality ceiling converts the paper's absolute `delta^eta*|J|`
   hypothesis to it. The new `pure_wz2_lemma66_normalized_interval`
   accepts an arbitrary supplied Prop. 6.4 configuration, with mass
   `(pi/4)*delta^(eta/16+2)*#family*|J|` and cap
   `delta^(2-sigma-eta/8192)*#family`. It derives the slab frame by
   retaining dense short global grains on that exact family. Thus frame
   preparation no longer requires a specially constructed configuration.
   Deriving the normalized mass and cap from the printed hypotheses is
   still open. `LargeSlopeTechnicalStatement` remains a separate,
   unproved older-model interface. The actual Node-6 assembly consumes
   `pureWZ2_c2_source_with_fine_cap`; the stronger universal-interval
   source endpoint is audited separately from the final root.
4. Node7b now normalizes Node 6's actual half-offset terminal. It chooses
   the source loss `a = analyticLoss/10000`, both normalization cutoffs and
   the source cutoff before calling Node 6. The latter proves
   `1+|safePublicSlope(0)| <= terminalDelta^(-a)`. The returned family,
   shading and public slope then enter `pure_wz2_paper_terminal_normalization_cutoff`.
   The coordinate map is `(x,y,z) -> (k(x+f(0)y),ky,z)`, with
   `k=1/(4(1+|f(0)|))`. A width-1/4 slab retains 1/12 of indexed mass;
   its exact image is retubed at radius `12*terminalDelta`, then cleaned up.
   `PureWZ2PaperTerminalProjectionRefinement` records injective source
   indices, exact supporting-line images, shading containment in the
   original slab image, and equality to the centered source slope.
   The projection-volume comparison with the actual original terminal is
   proved. The record now also proves `tube_eq_model`, so the common
   center height of the actual unit segments survives cleanup. The
   stronger `pure_wz2_node7b_common_height_from_retained_large_slope`
   retains this witness, and the old normalized output is its projection.
   No second configuration is selected from `commonSource`.

The compiled graph should show the prepared Lemma-6.6 theorem as a separate
node between C2 source preparation and the derivative-band construction.
Retain the distinction between type references and value references, and
inspect projections of stored witnesses when interpreting either graph.
