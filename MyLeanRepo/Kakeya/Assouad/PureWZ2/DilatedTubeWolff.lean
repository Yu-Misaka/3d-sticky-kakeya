import MyLeanRepo.Kakeya.Assouad.PureWZ2.FullLineTubeWolff
import MyLeanRepo.Kakeya.Assouad.PureWZ2.OrdinaryTubeWolff
import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.TubeRadius

/-!
# Finite coarse capsules with a fixed longitudinal margin

The coarse tests are centered dilations of ordinary unit-segment capsules.
At factor 32 they accommodate every longitudinal position in the bounded
chart. CWA supplies these tests directly. This is an explicit model
correction, not an implication from the refuted unit-length tests alone.
-/

noncomputable section
open MeasureTheory Set
namespace Kakeya.Assouad

/-- Tube Wolff tests with coarse axis length `factor`. The fine capsules are
unchanged. The physical coarse radius is `factor * r`. -/
def DilatedTubeWolffVolumeBound {delta : ℝ}
    (F : Kakeya.Streamlined.TubeFamily delta) (factor : ℝ) (C : ENNReal) : Prop :=
  ∀ r : ℝ, 0 < r → ∀ T : Kakeya.DeltaTube r,
    F.toBodyFamily.containedCount (wz2PaperCenteredDilatedCarrier factor T) ≤
      C * volume (wz2PaperCenteredDilatedCarrier factor T) * F.enncard

theorem dilatedTubeWolffVolumeBound_one_iff {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta} {C : ENNReal} :
    DilatedTubeWolffVolumeBound F 1 C ↔ OrdinaryTubeWolffVolumeBound F C := by
  simp [DilatedTubeWolffVolumeBound, OrdinaryTubeWolffVolumeBound,
    wz2PaperCenteredDilatedCarrier]

theorem dilatedTubeWolffVolumeBound_of_bodyConvexWolffBound
    {delta factor : ℝ} {F : Kakeya.Streamlined.TubeFamily delta} {C : ENNReal}
    (hcwa : WZ2PaperBodyConvexWolffBound F.toBodyFamily C) :
    DilatedTubeWolffVolumeBound F factor C := by
  intro r _ T
  exact hcwa _ ((wz2_paper_ordinary_tube_carrier_convex T).affine_image
    (AffineMap.homothety (wz2PaperTubeMidpoint T) factor))

theorem dilatedTubeWolffVolumeBound_of_convexWolffBound
    {delta factor : ℝ} {F : Kakeya.Streamlined.TubeFamily delta} {C : ENNReal}
    (hcwa : ConvexWolffBound F C) : DilatedTubeWolffVolumeBound F factor C := by
  apply dilatedTubeWolffVolumeBound_of_bodyConvexWolffBound
  have hunit : (1 : ENNReal) ≤ Kakeya.deltaTubeVolume 1 := by
    simpa using canonical_volume_lower (by norm_num : (0 : ℝ) < 1)
  intro K hK
  exact (le_mul_of_one_le_right' hunit).trans (hcwa K hK)

/-- A line neighborhood in the working ball lies in one finite coarse
capsule of length 32 and the same physical radius. -/
theorem fullLineTubeInBall_subset_dilated32
    {r : ℝ} (hr : 0 < r) (hrOne : r ≤ 1) (T : Kakeya.DeltaTube r)
    (hbase : ‖T.base‖ ≤ 4) :
    fullLineTubeInBall 6 T ⊆ wz2PaperCenteredDilatedCarrier 32
      (Kakeya.Streamlined.GeometricLemmas.withRadius (r / 32) T) := by
  rintro p ⟨hp, hpball⟩
  obtain ⟨q, ⟨t, ht⟩, hpq⟩ := exists_dist_le_of_mem_cthickening_closed
    (isClosed_tubeAxisLine T) hr.le hp
  have hpnorm : ‖p‖ ≤ 6 := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hpball
  have hqnorm : ‖q‖ ≤ 7 := by
    have h := norm_add_le (q - p) p
    rw [sub_add_cancel, ← dist_eq_norm, dist_comm q p] at h
    linarith
  have htAbs : |t| ≤ 11 := by
    have h : ‖q - T.base‖ ≤ ‖q‖ + ‖T.base‖ := norm_sub_le q T.base
    have heq : ‖q - T.base‖ = |t| := by
      rw [ht, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, T.direction_unit, mul_one]
    rw [heq] at h
    linarith
  let center := wz2PaperTubeMidpoint T
  let x := center + (1 / 32 : ℝ) • (p - center)
  let y := center + (1 / 32 : ℝ) • (q - center)
  let s := (1 / 2 : ℝ) + (t - 1 / 2) / 32
  have hs : s ∈ Set.Icc (0 : ℝ) 1 := by
    dsimp only [s]
    constructor <;> linarith [abs_le.mp htAbs]
  have hy : y = T.base + s • T.direction := by
    dsimp only [y, s, center, wz2PaperTubeMidpoint]
    rw [ht]
    module
  have hdist : dist x y ≤ r / 32 := by
    have hxy : x - y = (1 / 32 : ℝ) • (p - q) := by
      dsimp only [x, y]
      module
    rw [dist_eq_norm, hxy, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by norm_num : (0 : ℝ) < 1 / 32), ← dist_eq_norm]
    linarith
  have hx : x ∈ (Kakeya.Streamlined.GeometricLemmas.withRadius (r / 32) T).carrier := by
    apply Metric.mem_cthickening_of_dist_le x y (r / 32) _ _ hdist
    exact ⟨s, hs, hy.symm⟩
  refine ⟨x, hx, ?_⟩
  simp only [AffineMap.homothety_apply]
  change (32 : ℝ) • (x - center) + center = p
  dsimp only [x]
  module

/-- The fixed length costs only a constant in the radius-squared estimate. -/
theorem dilated32_volume_le {r : ℝ} (hr : 0 < r) (hrOne : r ≤ 1)
    (T : Kakeya.DeltaTube r) :
    volume (wz2PaperCenteredDilatedCarrier 32
      (Kakeya.Streamlined.GeometricLemmas.withRadius (r / 32) T)) ≤
      320 * Kakeya.realRpowENN r 2 := by
  rw [wz2_paper_centeredDilatedCarrier_volume]
  have h := ordinaryTube_volume_le_ten_radius_sq (by positivity : 0 < r / 32)
    (by linarith : r / 32 ≤ 1)
    (Kakeya.Streamlined.GeometricLemmas.withRadius (r / 32) T)
  calc
    _ ≤ ENNReal.ofReal (|(32 : ℝ)| ^ 3) * (10 * Kakeya.realRpowENN (r / 32) 2) := by gcongr
    _ = ENNReal.ofReal (32768 * (10 * (r / 32)^2)) := by
      norm_num [Kakeya.realRpowENN, ENNReal.ofReal_mul]
    _ = ENNReal.ofReal (320 * r^2) := by congr 1; ring
    _ = 320 * Kakeya.realRpowENN r 2 := by
      simp [Kakeya.realRpowENN, ENNReal.ofReal_mul]

/-- Fixed-length finite capsule tests imply parameter Frostman for arbitrary
longitudinal positions. The radius enlargement is 20 and the length is 32,
so the explicit constant is 320 * 20^2 = 128000. -/
theorem tubeParameterFrostmanBound_of_dilatedTubeWolffBound
    {delta : ℝ} (hdelta : 0 < delta)
    {F : Kakeya.Streamlined.TubeFamily delta}
    (hbase : HasBoundedBase F 4) (hvertical : IsInVerticalChart F)
    {C : ENNReal} (hC : 1 ≤ C) (hwolff : DilatedTubeWolffVolumeBound F 32 C) :
    TubeParameterFrostmanBound F (128000 * C) := by
  classical
  intro r hdeltaR hrOne reference
  have hr : 0 < r := hdelta.trans_le hdeltaR
  let indices := Finset.univ.filter fun i : Fin F.card =>
    |(tubeParams i).a - (tubeParams reference).a| ≤ r ∧
    |(tubeParams i).b - (tubeParams reference).b| ≤ r ∧
    |(tubeParams i).c - (tubeParams reference).c| ≤ r ∧
    |(tubeParams i).d - (tubeParams reference).d| ≤ r
  change (indices.card : ENNReal) ≤ _
  by_cases hsmall : r ≤ 1 / 20
  · let coarse : Kakeya.DeltaTube (20 * r) := {
      base := (F.tube reference).base
      direction := (F.tube reference).direction
      direction_unit := (F.tube reference).direction_unit }
    have hv : coarse.direction 2 ≠ 0 := by
      intro hzero
      have h := hvertical reference
      change (1 / 2 : ℝ) ≤ |coarse.direction 2| at h
      rw [hzero, abs_zero] at h
      norm_num at h
    let long := wz2PaperCenteredDilatedCarrier 32
      (Kakeya.Streamlined.GeometricLemmas.withRadius ((20 * r) / 32) coarse)
    have hsubset : indices ⊆ F.toBodyFamily.containedIndices long := by
      intro i hi
      apply Kakeya.Streamlined.BodyFamily.mem_containedIndices_iff.mpr
      intro p hp
      apply fullLineTubeInBall_subset_dilated32 (by positivity)
        (by linarith) coarse (hbase reference)
      have hprism := parameter_cluster_carrier_subset_widePrism hdelta hdeltaR hrOne
        hbase hvertical reference i (Finset.mem_filter.mp hi).2 hp
      have hline := wideTubeParameterPrism_subset_line_neighbourhood
        (by positivity : 0 ≤ 10 * r) coarse hv hprism
      refine ⟨?_, tube_carrier_subset_closedBall_six hdelta.le
        (hdeltaR.trans hrOne) (F.tube i) (hbase i) hp⟩
      simpa only [show 2 * (10 * r) = 20 * r by ring] using hline
    have hvolume : volume long ≤ 128000 * Kakeya.realRpowENN r 2 := by
      calc
        _ ≤ 320 * Kakeya.realRpowENN (20 * r) 2 :=
          dilated32_volume_le (by positivity) (by linarith) coarse
        _ = ENNReal.ofReal (320 * (20 * r)^2) := by
          simp [Kakeya.realRpowENN, ENNReal.ofReal_mul]
        _ = ENNReal.ofReal (128000 * r^2) := by congr 1; ring
        _ = _ := by simp [Kakeya.realRpowENN, ENNReal.ofReal_mul]
    calc
      _ ≤ F.toBodyFamily.containedCount long := by
        change (indices.card : ENNReal) ≤
          ((F.toBodyFamily.containedIndices long).card : ENNReal)
        exact_mod_cast Finset.card_le_card hsubset
      _ ≤ C * volume long * F.enncard :=
        hwolff ((20 * r) / 32) (by positivity)
          (Kakeya.Streamlined.GeometricLemmas.withRadius ((20 * r) / 32) coarse)
      _ ≤ C * (128000 * Kakeya.realRpowENN r 2) * F.enncard := by gcongr
      _ = _ := by ring
  · have hcount : (indices.card : ENNReal) ≤ F.enncard := by
      have h := Finset.card_le_card (Finset.filter_subset
        (fun i : Fin F.card =>
          |(tubeParams i).a - (tubeParams reference).a| ≤ r ∧
          |(tubeParams i).b - (tubeParams reference).b| ≤ r ∧
          |(tubeParams i).c - (tubeParams reference).c| ≤ r ∧
          |(tubeParams i).d - (tubeParams reference).d| ≤ r) Finset.univ)
      simpa [indices, Kakeya.Streamlined.TubeFamily.enncard] using
        (show ((Finset.univ.filter _).card : ENNReal) ≤
          ((Finset.univ : Finset (Fin F.card)).card : ENNReal) by exact_mod_cast h)
    have hfactor : (1 : ENNReal) ≤ 128000 * Kakeya.realRpowENN r 2 := by
      have hreal : (1 : ℝ) ≤ 128000 * r ^ 2 := by nlinarith
      simpa [Kakeya.realRpowENN, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 128000)] using
        ENNReal.ofReal_mono hreal
    calc
      _ ≤ F.enncard := hcount
      _ = 1 * F.enncard := (one_mul _).symm
      _ ≤ (128000 * Kakeya.realRpowENN r 2) * F.enncard := mul_le_mul_left hfactor _
      _ ≤ (128000 * C * Kakeya.realRpowENN r 2) * F.enncard := by
        calc
          _ = (128000 * 1 * Kakeya.realRpowENN r 2) * F.enncard := by rw [mul_one]
          _ ≤ _ := by gcongr

end Kakeya.Assouad
end
