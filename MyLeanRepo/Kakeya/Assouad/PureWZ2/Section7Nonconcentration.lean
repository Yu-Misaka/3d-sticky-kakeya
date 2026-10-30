import MyLeanRepo.Kakeya.Assouad.PureWZ2.WideParameterPrism
import MyLeanRepo.Kakeya.Assouad.TubeVolumeLowerBound

/-!
# The two geometric consequences of ordinary Convex Wolff

The ordinary capsule Tube-Wolff test and the indexed supporting-line count
are different predicates.  Here each is proved directly from Convex Wolff,
with its own quantitative constant.  In particular the second proof does
not presume a Tube-Wolff-to-parameter implication.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Assouad

/-- CWA specializes to the ordinary Tube-Wolff count.  The factor 24 is the
proved capsule-volume comparison; the unit tube volume cancels exactly. -/
theorem tubeWolffBound_of_convexWolffBound
    {delta : ℝ} (hdelta : 0 < delta)
    {F : Kakeya.Streamlined.TubeFamily delta} {C : ENNReal}
    (hcwa : ConvexWolffBound F C) :
    TubeWolffBound F (24 * C) := by
  intro rho hdeltaRho hrhoOne T
  have hrho : 0 < rho := hdelta.trans_le hdeltaRho
  have hcount := hcwa T.carrier (wz2_paper_ordinary_tube_carrier_convex T)
  have hvolume := tube_volume_scaling.2.2 rho hrho hrhoOne T
  have hunit := tube_volume_scaling.2.1 1 (by norm_num) le_rfl
  have hmain :
      F.toBodyFamily.containedCount T.carrier * Kakeya.deltaTubeVolume 1 ≤
        ((24 * C) * Kakeya.realRpowENN rho 2 * F.enncard) *
          Kakeya.deltaTubeVolume 1 := by
    calc
      _ ≤ C * volume T.carrier * F.enncard := hcount
      _ ≤ C * (24 * Kakeya.realRpowENN rho 2 *
          Kakeya.deltaTubeVolume 1) * F.enncard := by
            gcongr
            exact hvolume
      _ = _ := by ring
  have hcancel := mul_le_mul_right' hmain (Kakeya.deltaTubeVolume 1)⁻¹
  simpa only [mul_assoc, ENNReal.mul_inv_cancel hunit.1.ne' hunit.2,
    mul_one] using hcancel

/-- A width-r line-parameter cluster lies in the existing radius-10r,
height-12 prism, of volume at most 4800 r².  CWA therefore proves the
indexed parameter bound, including longitudinal multiplicity. -/
theorem tubeParameterFrostmanBound_of_bodyConvexWolffBound
    {delta : ℝ} (hdelta : 0 < delta)
    {F : Kakeya.Streamlined.TubeFamily delta}
    (hbase : HasBoundedBase F 4) (hvertical : IsInVerticalChart F)
    {C : ENNReal} (hcwa : WZ2PaperBodyConvexWolffBound F.toBodyFamily C) :
    TubeParameterFrostmanBound F (4800 * C) := by
  classical
  intro r hdeltaR hrOne reference
  have hr : 0 < r := hdelta.trans_le hdeltaR
  let indices := Finset.univ.filter fun i : Fin F.card =>
    |(tubeParams i).a - (tubeParams reference).a| ≤ r ∧
    |(tubeParams i).b - (tubeParams reference).b| ≤ r ∧
    |(tubeParams i).c - (tubeParams reference).c| ≤ r ∧
    |(tubeParams i).d - (tubeParams reference).d| ≤ r
  let prism := wideTubeParameterPrism (tubeParams reference) (10 * r)
  have hsubset : indices ⊆ F.toBodyFamily.containedIndices prism := by
    intro i hi
    exact Kakeya.Streamlined.BodyFamily.mem_containedIndices_iff.mpr
      (parameter_cluster_carrier_subset_widePrism hdelta hdeltaR hrOne
        hbase hvertical reference i (Finset.mem_filter.mp hi).2)
  have hcount : (indices.card : ENNReal) ≤
      F.toBodyFamily.containedCount prism := by
    change (indices.card : ENNReal) ≤
      ((F.toBodyFamily.containedIndices prism).card : ENNReal)
    exact_mod_cast Finset.card_le_card hsubset
  have hgeometry := wideTubeParameterPrism_geometry
    (tubeParams reference) (10 * r) (by positivity)
  have hvolume : volume prism ≤ 4800 * Kakeya.realRpowENN r 2 := by
    calc
      _ ≤ ENNReal.ofReal (48 * (10 * r) ^ 2) := hgeometry.2
      _ = ENNReal.ofReal (4800 * r ^ 2) := by congr 1 <;> ring
      _ = _ := by
        simp [Kakeya.realRpowENN, Real.rpow_two,
          ENNReal.ofReal_mul (show (0 : ℝ) ≤ 4800 by norm_num)]
  change (indices.card : ENNReal) ≤ _
  calc
    _ ≤ F.toBodyFamily.containedCount prism := hcount
    _ ≤ C * volume prism * F.enncard := hcwa prism hgeometry.1
    _ ≤ C * (4800 * Kakeya.realRpowENN r 2) * F.enncard := by gcongr
    _ = _ := by ring

/-- The volume-normalized ordinary CWA interface gives the same parameter
constant, since the canonical unit tube has volume at least one. -/
theorem tubeParameterFrostmanBound_of_convexWolffBound
    {delta : ℝ} (hdelta : 0 < delta)
    {F : Kakeya.Streamlined.TubeFamily delta}
    (hbase : HasBoundedBase F 4) (hvertical : IsInVerticalChart F)
    {C : ENNReal} (hcwa : ConvexWolffBound F C) :
    TubeParameterFrostmanBound F (4800 * C) := by
  have hunit : (1 : ENNReal) ≤ Kakeya.deltaTubeVolume 1 := by
    simpa using canonical_volume_lower (by norm_num : (0 : ℝ) < 1)
  apply tubeParameterFrostmanBound_of_bodyConvexWolffBound hdelta hbase hvertical
  intro K hK
  exact (le_mul_of_one_le_right' hunit).trans (hcwa K hK)

end Kakeya.Assouad
