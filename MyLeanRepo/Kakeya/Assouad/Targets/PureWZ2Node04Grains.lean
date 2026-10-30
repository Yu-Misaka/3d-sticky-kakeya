import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.ADBridge
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Strategy1Main
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Strategy2Main
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63M9Main

import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.ReentrantEntry

/-!
# Pure WZ2 Node 4: grains

The public statement is projected from the M9 reentrant construction used by
Node 5.  Both grain records, the volume floor, and the ordinary trace therefore
belong to the same retained shading; the paper projection weakens only loss.
The earlier range-specific proofs remain available in their own modules.
-/

namespace Kakeya.Assouad

theorem pure_wz2_node04_grains :
    PureWZ2GrainsStatement := by
  intro h_subunit h_extraction h_sticky
  rcases h_sticky h_subunit h_extraction with ⟨capability⟩
  exact ⟨pure_wz2_paper_ad_bridge,
    (pure_wz2_node04_reentrant_grains capability).toGrainsFromCritical⟩

end Kakeya.Assouad
