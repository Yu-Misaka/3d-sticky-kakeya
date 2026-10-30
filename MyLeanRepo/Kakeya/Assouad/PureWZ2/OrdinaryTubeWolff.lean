import MyLeanRepo.Kakeya.Assouad.Definitions
import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.CapsuleVolume
import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.TubeVolume
import MyLeanRepo.Kakeya.Assouad.TubeVolumeLowerBound
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# The ordinary Tube Wolff condition with actual tube volume

The paper tests all positive-radius ordinary unit-segment tubes and uses
their actual volume. The repository's `TubeWolffBound` instead uses r^2 on
delta <= r <= 1. These conventions are equivalent up to a fixed constant.
Containment in a tube of radius below delta is impossible by strict volume
monotonicity, and radii above one are controlled by total cardinality.
-/

noncomputable section
open MeasureTheory Set
namespace Kakeya.Assouad

def OrdinaryTubeWolffVolumeBound {delta : ℝ}
    (F : Kakeya.Streamlined.TubeFamily delta) (C : ENNReal) : Prop :=
  ∀ r : ℝ, 0 < r → ∀ T : Kakeya.DeltaTube r,
    F.toBodyFamily.containedCount T.carrier ≤ C * volume T.carrier * F.enncard

/-- CWA supplies the paper's actual-volume ordinary tube tests directly. -/
theorem ordinaryTubeWolffVolumeBound_of_convexWolffBound
    {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta} {C : ENNReal}
    (hcwa : ConvexWolffBound F C) : OrdinaryTubeWolffVolumeBound F C := by
  have hunit : (1 : ENNReal) ≤ Kakeya.deltaTubeVolume 1 := by
    simpa using canonical_volume_lower (by norm_num : (0 : ℝ) < 1)
  intro r _ T
  exact (le_mul_of_one_le_right' hunit).trans
    (hcwa T.carrier (wz2_paper_ordinary_tube_carrier_convex T))

theorem ordinaryTube_volume_eq {r : ℝ} (hr : 0 < r) (T : Kakeya.DeltaTube r) :
    volume T.carrier = ENNReal.ofReal
      (Real.pi * r ^ 2 + (4 / 3 : ℝ) * Real.pi * r ^ 3) := by
  let canonical : Kakeya.DeltaTube r :=
    { base := 0
      direction := EuclideanSpace.single (0 : Fin 3) 1
      direction_unit := by simp }
  have h := Kakeya.Streamlined.tube_volume_eq T canonical
  change volume T.carrier = volume canonical.carrier at h
  rw [h]
  simpa only [canonical, Kakeya.DeltaTube.carrier,
    Kakeya.Streamlined.GeometricLemmas.capsule,
    Kakeya.Streamlined.GeometricLemmas.unitSegment0e0] using
      Kakeya.Streamlined.GeometricLemmas.capsule_volume_exact r hr

theorem ordinaryTube_radius_sq_le_volume {r : ℝ} (hr : 0 < r)
    (T : Kakeya.DeltaTube r) : Kakeya.realRpowENN r 2 ≤ volume T.carrier := by
  rw [ordinaryTube_volume_eq hr T]
  have h : r ^ 2 ≤ Real.pi * r ^ 2 + (4 / 3 : ℝ) * Real.pi * r ^ 3 := by
    have hpi := Real.pi_gt_three
    have hcube : 0 ≤ (4 / 3 : ℝ) * Real.pi * r ^ 3 := by positivity
    nlinarith [sq_nonneg r]
  have hpower : Real.rpow r 2 = r ^ 2 := Real.rpow_two r
  change ENNReal.ofReal (Real.rpow r 2) ≤ _
  rw [hpower]
  exact ENNReal.ofReal_mono h

theorem ordinaryTube_volume_le_ten_radius_sq {r : ℝ} (hr : 0 < r)
    (hrOne : r ≤ 1) (T : Kakeya.DeltaTube r) :
    volume T.carrier ≤ 10 * Kakeya.realRpowENN r 2 := by
  rw [ordinaryTube_volume_eq hr T]
  have hcube : r ^ 3 ≤ r ^ 2 := by nlinarith [sq_nonneg r]
  have h : Real.pi * r ^ 2 + (4 / 3 : ℝ) * Real.pi * r ^ 3 ≤ 10 * r ^ 2 := by
    have hpi := Real.pi_lt_four
    have h3 := mul_le_mul_of_nonneg_left hcube (by positivity : 0 ≤ (4 / 3 : ℝ) * Real.pi)
    nlinarith [sq_nonneg r]
  have hENN := ENNReal.ofReal_mono h
  simpa [Kakeya.realRpowENN, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 10)] using hENN

theorem ordinaryTube_not_subset_of_radius_lt {r delta : ℝ}
    (hr : 0 < r) (hrd : r < delta) (S : Kakeya.DeltaTube delta) (T : Kakeya.DeltaTube r) :
    ¬ S.carrier ⊆ T.carrier := by
  have hdelta : 0 < delta := hr.trans hrd
  have hsq : r ^ 2 < delta ^ 2 := pow_lt_pow_left₀ hrd hr.le (by norm_num)
  have hcube : r ^ 3 < delta ^ 3 := pow_lt_pow_left₀ hrd hr.le (by norm_num)
  have hformula : Real.pi * r ^ 2 + (4 / 3 : ℝ) * Real.pi * r ^ 3 <
      Real.pi * delta ^ 2 + (4 / 3 : ℝ) * Real.pi * delta ^ 3 :=
    add_lt_add (mul_lt_mul_of_pos_left hsq Real.pi_pos)
      (mul_lt_mul_of_pos_left hcube (by positivity))
  have hvolume : volume T.carrier < volume S.carrier := by
    rw [ordinaryTube_volume_eq hr, ordinaryTube_volume_eq (hr.trans hrd)]
    exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 hformula
  exact fun h => (not_le_of_gt hvolume) (measure_mono h)

theorem TubeWolffBound.to_ordinaryVolume {delta : ℝ}
    (hdelta : 0 < delta) {F : Kakeya.Streamlined.TubeFamily delta}
    {C : ENNReal} (hC : 1 ≤ C) (hF : TubeWolffBound F C) :
    OrdinaryTubeWolffVolumeBound F C := by
  classical
  intro r hr T
  by_cases hdr : delta ≤ r
  · by_cases hrOne : r ≤ 1
    · exact (hF r hdr hrOne T).trans (by
        gcongr
        exact ordinaryTube_radius_sq_le_volume hr T)
    · have hvol : 1 ≤ volume T.carrier := by
        have hsquare : (1 : ℝ) ≤ r ^ 2 := by nlinarith
        have hpower : (1 : ENNReal) ≤ Kakeya.realRpowENN r 2 := by
          simpa [Kakeya.realRpowENN] using ENNReal.ofReal_mono hsquare
        exact hpower.trans (ordinaryTube_radius_sq_le_volume hr T)
      have hcount : F.toBodyFamily.containedCount T.carrier ≤ F.enncard := by
        have h := Finset.card_le_card (Finset.subset_univ
          (F.toBodyFamily.containedIndices T.carrier))
        have hsize : (Finset.univ : Finset (Fin F.toBodyFamily.card)).card = F.card :=
          (Finset.card_univ).trans (Fintype.card_fin F.card)
        change ((F.toBodyFamily.containedIndices T.carrier).card : ENNReal) ≤ (F.card : ENNReal)
        exact_mod_cast h.trans_eq hsize
      calc
        _ ≤ F.enncard := hcount
        _ = 1 * 1 * F.enncard := by simp
        _ ≤ _ := by gcongr
  · have hempty : F.toBodyFamily.containedIndices T.carrier = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i hi
      exact ordinaryTube_not_subset_of_radius_lt hr (lt_of_not_ge hdr) (F.tube i) T
        (Kakeya.Streamlined.BodyFamily.mem_containedIndices_iff.mp hi)
    change ((F.toBodyFamily.containedIndices T.carrier).card : ENNReal) ≤ _
    rw [hempty, Finset.card_empty, Nat.cast_zero]
    positivity

theorem OrdinaryTubeWolffVolumeBound.to_radiusSquared {delta : ℝ}
    (hdelta : 0 < delta) {F : Kakeya.Streamlined.TubeFamily delta}
    {C : ENNReal} (hF : OrdinaryTubeWolffVolumeBound F C) :
    TubeWolffBound F (10 * C) := by
  intro r hdr hrOne T
  have hr := hdelta.trans_le hdr
  calc
    _ ≤ C * volume T.carrier * F.enncard := hF r hr T
    _ ≤ C * (10 * Kakeya.realRpowENN r 2) * F.enncard := by
      gcongr
      exact ordinaryTube_volume_le_ten_radius_sq hr hrOne T
    _ = _ := by ring

end Kakeya.Assouad
end
