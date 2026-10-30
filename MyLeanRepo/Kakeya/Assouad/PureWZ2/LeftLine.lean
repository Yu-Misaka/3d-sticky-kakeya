import MyLeanRepo.Kakeya.Assouad.PureWZ2.SubunitPackage
import MyLeanRepo.Kakeya.Assouad.Targets.PureWZ2Node02CriticalExtraction
import MyLeanRepo.Kakeya.Assouad.Targets.PureWZ2Node03PropSticky
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05V4RichFinalAssembly
import MyLeanRepo.Kakeya.Assouad.Targets.PureWZ2Node06LargeSlope
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Node7FromCritical
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Node7bPreparation
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.IntervalReadyC2Source
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.Lemma66NormalizedInterval

/-!
# Closed left-line upper bounds, stopping at WZ2 Lemma 6.7

These entries have no external proof inputs.  As in the paper's Section 6,
the conclusions are conditional only on a positive critical package.  No
projection lower bound or final contradiction is used here.

Node 5 consumes the reentrant Proposition 6.3 grains.  The derivative step
uses the independent prepared-slab Lemma 6.6.  Node 6 retains its completed
paper terminal.  Its actual family, shading and slope are transported by
the proved slope-offset map, slab restriction and analytic cleanup.

The imported normalized-interval lemma now accepts every supplied C2
configuration and constructs the slab frame internally. Its normalized
mass and fine multiplicity hypotheses remain explicit; the printed
absolute-mass Lemma 6.6 is not asserted.
The normalized endpoint retains controlled transport from the paper terminal;
it does not assert equality of families before and after the coordinate change.
-/

noncomputable section
namespace Kakeya.Assouad

/-- Closed Proposition 6.4 using the actual reentrant Proposition 6.3 output. -/
theorem pure_wz2_left_line_c2_grains : PureWZ2C2GrainsFromCriticalStatement := by
  rcases pure_wz2_node03_prop_sticky pure_wz2_node01_subunit_package
      pure_wz2_node02_critical_extraction with ⟨capability⟩
  exact pureWZ2_c2_grains_from_reentrant capability pure_wz2_paper_ad_bridge
    (pure_wz2_node04_reentrant_grains capability)

/-- One actual C2 source and global fine cap, chosen before the interval,
support the normalized arbitrary-interval derivative lemma. Its frame and
whole-cell preparation are constructed on each later supplied slab. -/
theorem pure_wz2_left_line_c2_prescribed_intervals :
    PureWZ2C2PrescribedIntervalsStatement := by
  obtain ⟨logExponent, provider⟩ :=
    Prop62PaperAudit.V4.Prop62V4DirectNode6FixedScaleCertified.fixedScaleStatement
  exact pureWZ2_c2_source_with_prescribed_intervals pure_wz2_left_line_c2_grains provider

/-- Closed Proposition 6.5 with the witnesses needed by either Lemma 6.7
consumer; both source and target scale ceilings are caller-controlled. -/
theorem pure_wz2_left_line_large_slope_retained :
    PureWZ2LargeSlopeRetainedStatement :=
  pure_wz2_node06_large_slope_retained pure_wz2_left_line_c2_grains

/-- Closed paper-facing Lemma 6.7, with the blueprint's corrected exponent
`sigma - outputLoss`.  No external node proofs occur in the statement. -/
theorem pure_wz2_left_line_lemma67 :
    PureWZ2SmallTwistedProjectionFromCriticalStatement :=
  pure_wz2_node7_from_large_slope
    pure_wz2_left_line_large_slope_retained.toLargeSlopeFromCritical

/-- The final upper bound and CWA, with every lower-bound normalization,
on a single ordinary family, shading, and slope. -/
theorem pure_wz2_left_line_common_height_projection :
    PureWZ2CommonHeightProjectionStatement :=
  pure_wz2_node7b_common_height_from_retained_large_slope
    pure_wz2_left_line_large_slope_retained

/-- Historical normalized upper bound on the same common-height terminal. -/
theorem pure_wz2_left_line_normalized_projection :
    PureWZ2NormalizedProjectionStatement :=
  pure_wz2_node7b_normalized_from_retained_large_slope
    pure_wz2_left_line_large_slope_retained

/-- Closed analytic preparation from the actual completed Node-6 terminal. -/
theorem pure_wz2_left_line_lemma67_preparation :
    PureWZ2ParameterFrostmanPreparationStatement :=
  pure_wz2_node7b_from_retained_large_slope
    pure_wz2_left_line_large_slope_retained

end Kakeya.Assouad
end
