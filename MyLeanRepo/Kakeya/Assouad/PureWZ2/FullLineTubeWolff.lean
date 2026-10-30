import MyLeanRepo.Kakeya.Assouad.PureWZ2.Section7Nonconcentration
import MyLeanRepo.Kakeya.Assouad.PureWZ2.BoundedDeltaMax
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperTubeCarrierGeometryHelpers

/-!
# Tube Wolff tests on full lines in a fixed spatial window

The coarse test is a Euclidean neighbourhood of an entire supporting line,
intersected with a fixed ball.  Its definition does not use line parameters.
This differs from the historical `TubeWolffBound`, whose tests are capsules
around unit segments.  We prove the geometric parameter-count reduction for
these windowed full-line tests, without presuming a reduction from capsules.
-/

noncomputable section
open MeasureTheory Set
namespace Kakeya.Assouad

/-- A radius-r full-line tube clipped to a ball of radius R. -/
def fullLineTubeInBall (R : ℝ) {r : ℝ} (T : Kakeya.DeltaTube r) : Set Point3 :=
  Metric.cthickening r (tubeAxisLine T) ∩ Metric.closedBall (0 : Point3) R

/-- Physical Tube Wolff counting with windowed full-line coarse tests.
The fine bodies remain the given ordinary tubes, including their indices. -/
def FullLineTubeWolffBound {delta : ℝ}
    (F : Kakeya.Streamlined.TubeFamily delta) (R : ℝ) (C : ENNReal) : Prop :=
  ∀ r : ℝ, delta ≤ r → r ≤ 1 → ∀ T : Kakeya.DeltaTube r,
    F.toBodyFamily.containedCount (fullLineTubeInBall R T) ≤
      C * volume (fullLineTubeInBall R T) * F.enncard

theorem fullLineTubeInBall_convex (R : ℝ) {r : ℝ} (T : Kakeya.DeltaTube r) :
    Convex ℝ (fullLineTubeInBall R T) :=
  ((convex_tubeAxisLine T).cthickening r).inter (convex_closedBall _ _)

/-- CWA applies to the actual full-line test, in every orientation. -/
theorem fullLineTubeWolffBound_of_bodyConvexWolffBound
    {delta R : ℝ} {F : Kakeya.Streamlined.TubeFamily delta} {C : ENNReal}
    (hcwa : WZ2PaperBodyConvexWolffBound F.toBodyFamily C) :
    FullLineTubeWolffBound F R C := by
  intro r _ _ T
  exact hcwa _ (fullLineTubeInBall_convex R T)

/-- The volume-normalized CWA also supplies the full-line tests. -/
theorem fullLineTubeWolffBound_of_convexWolffBound
    {delta R : ℝ} (hdelta : 0 < delta)
    {F : Kakeya.Streamlined.TubeFamily delta} {C : ENNReal}
    (hcwa : ConvexWolffBound F C) : FullLineTubeWolffBound F R C := by
  apply fullLineTubeWolffBound_of_bodyConvexWolffBound
  have hunit : (1 : ENNReal) ≤ Kakeya.deltaTubeVolume 1 := by
    simpa using canonical_volume_lower (by norm_num : (0 : ℝ) < 1)
  intro K hK
  exact (le_mul_of_one_le_right' hunit).trans (hcwa K hK)

private theorem affine_residual_le_three
    {x z x' z' a c r : ℝ} (hr : 0 ≤ r)
    (hx : |x - x'| ≤ r) (hz : |z - z'| ≤ r)
    (hline : x' = a + c * z') (hc : |c| ≤ 2) :
    |x - (a + c * z)| ≤ 3 * r := by
  have hdecomp : x - (a + c * z) = (x - x') + c * (z' - z) := by
    rw [hline]
    ring
  rw [hdecomp]
  calc
    _ ≤ |x - x'| + |c| * |z' - z| := by
      simpa only [abs_mul] using abs_add_le (x - x') (c * (z' - z))
    _ ≤ r + 2 * r := by
      gcongr
      simpa only [abs_sub_comm] using hz
    _ = 3 * r := by ring

/-- In a vertical chart the Euclidean tube test has a uniform volume bound.
This is an enclosure of a physical line neighbourhood, not a definition in
parameter coordinates. -/
theorem fullLineTubeInBall_six_volume_le
    {r : ℝ} (hr : 0 ≤ r) (T : Kakeya.DeltaTube r)
    (hvertical : T.direction 2 ≠ 0)
    (hslopes : |(tubeParamsOfTube T).c| ≤ 2 ∧ |(tubeParamsOfTube T).d| ≤ 2) :
    volume (fullLineTubeInBall 6 T) ≤ ENNReal.ofReal (432 * r ^ 2) := by
  have hsubset : fullLineTubeInBall 6 T ⊆
      wideTubeParameterPrism (tubeParamsOfTube T) (3 * r) := by
    intro p hp
    obtain ⟨q, hq, hpq⟩ := exists_dist_le_of_mem_cthickening_closed
      (isClosed_tubeAxisLine T) hr hp.1
    have hcoord (i : Fin 3) : |p i - q i| ≤ r :=
      (PiLp.norm_apply_le (p - q) i).trans (by simpa [dist_eq_norm] using hpq)
    have hnorm : ‖p‖ ≤ 6 := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hp.2
    exact ⟨abs_le.mp ((PiLp.norm_apply_le p 2).trans hnorm),
      affine_residual_le_three hr (hcoord 0) (hcoord 2)
        (tubeAxisLine_coord_zero T hvertical hq) hslopes.1,
      affine_residual_le_three hr (hcoord 1) (hcoord 2)
        (tubeAxisLine_coord_one T hvertical hq) hslopes.2⟩
  calc
    _ ≤ volume (wideTubeParameterPrism (tubeParamsOfTube T) (3 * r)) :=
      measure_mono hsubset
    _ ≤ ENNReal.ofReal (48 * (3 * r) ^ 2) :=
      (wideTubeParameterPrism_geometry _ _ (by positivity)).2
    _ = _ := by congr 1; ring

/-- A point in the vertical prism is close to the actual supporting line
at the same height. -/
theorem wideTubeParameterPrism_subset_line_neighbourhood
    {delta w : ℝ} (hw : 0 ≤ w) (T : Kakeya.DeltaTube delta)
    (hvertical : T.direction 2 ≠ 0) :
    wideTubeParameterPrism (tubeParamsOfTube T) w ⊆
      Metric.cthickening (2 * w) (tubeAxisLine T) := by
  intro p hp
  let q := tubeAxisPointAtHeight T (p 2)
  have hq0 := tubeAxisPointAtHeight_coord_zero T hvertical (p 2)
  have hq1 := tubeAxisPointAtHeight_coord_one T hvertical (p 2)
  have hq2 := tubeAxisPointAtHeight_coord_two T hvertical (p 2)
  have hx : |(p - q) 0| ≤ w := by
    simpa only [PiLp.sub_apply, q, hq0] using hp.2.1
  have hy : |(p - q) 1| ≤ w := by
    simpa only [PiLp.sub_apply, q, hq1] using hp.2.2
  have hz : (p - q) 2 = 0 := by simp only [PiLp.sub_apply, q, hq2, sub_self]
  have hnorm := point3_coord_norm_sq (p - q)
  have hx2 : (p - q) 0 ^ 2 ≤ w ^ 2 := by
    nlinarith [abs_le.mp hx, sq_abs ((p - q) 0)]
  have hy2 : (p - q) 1 ^ 2 ≤ w ^ 2 := by
    nlinarith [abs_le.mp hy, sq_abs ((p - q) 1)]
  have hdist : dist p q ≤ 2 * w := by
    rw [dist_eq_norm]
    rw [hz] at hnorm
    nlinarith [norm_nonneg (p - q)]
  exact Metric.mem_cthickening_of_dist_le p q (2 * w) _
    (tubeAxisPointAtHeight_mem T (p 2)) hdist

/-- Tube Wolff on full-line tests implies indexed parameter Frostman.
The factor 172800 is the explicit radius enlargement and volume bound.
No convex-set count is used in this implication. -/
theorem tubeParameterFrostmanBound_of_fullLineTubeWolffBound
    {delta : ℝ} (hdelta : 0 < delta)
    {F : Kakeya.Streamlined.TubeFamily delta}
    (hbase : HasBoundedBase F 4) (hvertical : IsInVerticalChart F)
    {C : ENNReal} (hC : 1 ≤ C) (hwolff : FullLineTubeWolffBound F 6 C) :
    TubeParameterFrostmanBound F (172800 * C) := by
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
    have hslopes : |(tubeParamsOfTube coarse).c| ≤ 2 ∧
        |(tubeParamsOfTube coarse).d| ≤ 2 := tubeParams_cd_bounds hvertical reference
    have hsubset : indices ⊆ F.toBodyFamily.containedIndices (fullLineTubeInBall 6 coarse) := by
      intro i hi
      apply Kakeya.Streamlined.BodyFamily.mem_containedIndices_iff.mpr
      intro p hp
      have hprism := parameter_cluster_carrier_subset_widePrism hdelta hdeltaR hrOne
        hbase hvertical reference i (Finset.mem_filter.mp hi).2 hp
      have hline := wideTubeParameterPrism_subset_line_neighbourhood
        (by positivity : 0 ≤ 10 * r) coarse hv hprism
      refine ⟨?_, tube_carrier_subset_closedBall_six hdelta.le
        (hdeltaR.trans hrOne) (F.tube i) (hbase i) hp⟩
      simpa only [show 2 * (10 * r) = 20 * r by ring] using hline
    have hvolume : volume (fullLineTubeInBall 6 coarse) ≤
        172800 * Kakeya.realRpowENN r 2 := by
      calc
        _ ≤ ENNReal.ofReal (432 * (20 * r) ^ 2) :=
          fullLineTubeInBall_six_volume_le (by positivity) coarse hv hslopes
        _ = ENNReal.ofReal (172800 * r ^ 2) := by congr 1; ring
        _ = _ := by
          simp [Kakeya.realRpowENN, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 172800)]
    calc
      _ ≤ F.toBodyFamily.containedCount (fullLineTubeInBall 6 coarse) := by
        change (indices.card : ENNReal) ≤
          ((F.toBodyFamily.containedIndices (fullLineTubeInBall 6 coarse)).card : ENNReal)
        exact_mod_cast Finset.card_le_card hsubset
      _ ≤ C * volume (fullLineTubeInBall 6 coarse) * F.enncard :=
        hwolff (20 * r) (by linarith) (by linarith) coarse
      _ ≤ C * (172800 * Kakeya.realRpowENN r 2) * F.enncard := by gcongr
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
    have hfactor : (1 : ENNReal) ≤ 172800 * Kakeya.realRpowENN r 2 := by
      have hreal : (1 : ℝ) ≤ 172800 * r ^ 2 := by nlinarith
      simpa [Kakeya.realRpowENN, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 172800)] using
        ENNReal.ofReal_mono hreal
    calc
      _ ≤ F.enncard := hcount
      _ = 1 * F.enncard := (one_mul _).symm
      _ ≤ (172800 * Kakeya.realRpowENN r 2) * F.enncard := mul_le_mul_left hfactor _
      _ ≤ (172800 * C * Kakeya.realRpowENN r 2) * F.enncard := by
        calc
          _ = (172800 * 1 * Kakeya.realRpowENN r 2) * F.enncard := by rw [mul_one]
          _ ≤ _ := by gcongr

end Kakeya.Assouad
end
