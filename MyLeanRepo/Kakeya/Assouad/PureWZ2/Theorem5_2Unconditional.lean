import MyLeanRepo.Kakeya.Assouad.PureWZ2.SubunitPackage
import MyLeanRepo.Kakeya.Assouad.Targets.PureWZ2Node02CriticalExtraction
import MyLeanRepo.Kakeya.Assouad.Targets.PureWZ2Node03PropSticky
import MyLeanRepo.Kakeya.Assouad.Targets.PureWZ2Node04Grains
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05V4RichFinalAssembly
import MyLeanRepo.Kakeya.Assouad.Targets.PureWZ2Node06LargeSlope
import MyLeanRepo.Kakeya.Assouad.Targets.PureWZ2Node07SmallTwistedProjection
import MyLeanRepo.Kakeya.Assouad.Targets.PureWZ2Node08Theorem5_2
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LeftLine
import MyLeanRepo.Kakeya.Assouad.PureWZ2.NormalizedContradiction
import MyLeanRepo.Kakeya.Assouad.PureWZ2.CommonHeightContradiction

/-!
# Unconditional pure WZ2 Theorem 5.2

Critical extraction supplies the positive critical package.  The retained
left-line construction supplies one normalized terminal with both CWA and
the small projection upper bound.  The independent normalized CWA lower
bound is evaluated on that same terminal by `CommonHeightContradiction`.
The actual common-height unit segments are retained through cleanup, so
the lower bound follows the ordinary capsule Tube Wolff specialization.

The Node-5 input is `pure_wz2_left_line_c2_grains`, which passes the
reentrant grain witness to `pureWZ2_c2_grains_from_reentrant`.  The original
direct-rich construction keeps family, shading, nearby CWA, density,
volume upper, and both grains on the same combined-selection witness.
-/

noncomputable section

namespace Kakeya.Assouad

/-- The normalized pure WZ2 Theorem 5.2 with no external proof inputs. -/
theorem PureWZ2Theorem5_2Unconditional :
    PureWZ2Theorem5_2Statement :=
  pure_wz2_theorem5_2_of_common_height_projection
    pure_wz2_node01_subunit_package
    pure_wz2_node02_critical_extraction
    pure_wz2_left_line_common_height_projection

/-- Snake-case compatibility name for the unconditional endpoint. -/
theorem pure_wz2_theorem5_2_unconditional :
    PureWZ2Theorem5_2Statement :=
  PureWZ2Theorem5_2Unconditional

end Kakeya.Assouad

end
