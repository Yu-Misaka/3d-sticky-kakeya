import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.WeightedPopularGlobalGrains

/-!
# Retain dense cell packets by their actual incidence mass

Any finite labelling of the occupied cells can be used.  A pointwise
multiplicity cap converts a heavy packet's incidence mass to a spatial
volume floor.  The selection retains at least half of the supplied shading,
so it can be performed after an interval has been prescribed.
-/

noncomputable section
open MeasureTheory Set
namespace Kakeya.Assouad
attribute [local instance] Classical.propDecidable

theorem wz2RefinedShading_all_active_mass
    {delta : ℝ} {family : Kakeya.Streamlined.TubeFamily delta}
    (Z : WZ1PaperTubeShading family) (hdelta : 0 < delta)
    (hcubical : WZ1PaperIsCubicalShading Z) :
    (wz2RefinedShading Z (wz1PaperActiveCells Z hdelta)).mass = Z.mass := by
  have hcarrier : ∀ i,
      (wz2RefinedShading Z (wz1PaperActiveCells Z hdelta)).carrier i = Z.carrier i := by
    intro i
    apply Set.Subset.antisymm Set.inter_subset_left
    intro p hp
    refine ⟨hp, ?_⟩
    have h : p ∈ Z.union := ⟨i, hp⟩
    rwa [hcubical.union_eq_activeCells hdelta] at h
  apply Finset.sum_congr rfl
  intro i _
  rw [hcarrier]

theorem wz2RefinedShading_label_mass_sum
    {delta : ℝ} {family : Kakeya.Streamlined.TubeFamily delta}
    (Z : WZ1PaperTubeShading family)
    {Label : Type*} [DecidableEq Label]
    (label : WZ2PaperCellIndex → Label)
    (cells : Finset WZ2PaperCellIndex) (labels : Finset Label) :
    (∑ l ∈ labels, (wz2RefinedShading Z (cells.filter fun c => label c = l)).mass) =
      (wz2RefinedShading Z (cells.filter fun c => label c ∈ labels)).mass := by
  simp_rw [wz2RefinedShading_mass_eq_sum_cells]
  exact Finset.sum_fiberwise_eq_sum_filter cells labels label _

/-- Select heavy packets on the same family and in the supplied shading.
The density condition concerns the original packet, whose local AD data
remain available even if other packets are discarded. -/
theorem pureWZ2_dense_cell_label_refinement
    {delta : ℝ} {family : Kakeya.Streamlined.TubeFamily delta}
    (Z : WZ1PaperTubeShading family) (hdelta : 0 < delta)
    (hcubical : WZ1PaperIsCubicalShading Z)
    {Label : Type*} [DecidableEq Label]
    (label : WZ2PaperCellIndex → Label)
    (cap threshold : ENNReal) (hcapZero : cap ≠ 0) (hcapTop : cap ≠ ⊤)
    (hthresholdTop : threshold ≠ ⊤)
    (hcap : ∀ p, (Z.pointMultiplicity p : ENNReal) ≤ cap)
    (hbudget : 2 *
        (((wz1PaperActiveCells Z hdelta).image label).card : ENNReal) *
          (cap * threshold) ≤ Z.mass) :
    ∃ kept : Finset Label,
      kept ⊆ (wz1PaperActiveCells Z hdelta).image label ∧
      Z.mass ≤ 2 * (wz2RefinedShading Z
        ((wz1PaperActiveCells Z hdelta).filter fun c => label c ∈ kept)).mass ∧
      ∀ l ∈ kept, threshold ≤ volume
        (wz2RefinedShading Z
          ((wz1PaperActiveCells Z hdelta).filter fun c => label c = l)).union := by
  let cells := wz1PaperActiveCells Z hdelta
  let labels := cells.image label
  let weight := fun l => (wz2RefinedShading Z (cells.filter fun c => label c = l)).mass
  let kept := labels.filter fun l => cap * threshold ≤ weight l
  have htotal : (∑ l ∈ labels, weight l) = Z.mass := by
    rw [show (∑ l ∈ labels, weight l) =
      (wz2RefinedShading Z (cells.filter fun c => label c ∈ labels)).mass from
        wz2RefinedShading_label_mass_sum Z label cells labels]
    have hfilter : cells.filter (fun c => label c ∈ labels) = cells := by
      exact Finset.filter_eq_self.mpr (fun c hc => Finset.mem_image_of_mem label hc)
    rw [hfilter]
    exact wz2RefinedShading_all_active_mass Z hdelta hcubical
  have hretention := finite_sum_le_two_mul_heavy_sum labels weight (cap * threshold)
    (ENNReal.mul_ne_top hcapTop hthresholdTop) (by
      rw [htotal]
      simpa only [mul_assoc] using hbudget)
  refine ⟨kept, Finset.filter_subset _ _, ?_, ?_⟩
  · rw [htotal] at hretention
    have hsum : (∑ l ∈ kept, weight l) =
        (wz2RefinedShading Z (cells.filter fun c => label c ∈ kept)).mass :=
      wz2RefinedShading_label_mass_sum Z label cells kept
    calc
      Z.mass ≤ 2 * ∑ l ∈ kept, weight l := by simpa only [kept] using hretention
      _ = _ := by rw [hsum]
  · intro l hl
    let packet := wz2RefinedShading Z (cells.filter fun c => label c = l)
    have hpacketCap : ∀ p ∈ packet.union,
        (packet.pointMultiplicity p : ENNReal) ≤ cap := by
      intro p _
      have hnat : packet.pointMultiplicity p ≤ Z.pointMultiplicity p := by
        apply Finset.card_le_card
        intro i hi
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2.1⟩
      exact (show (packet.pointMultiplicity p : ENNReal) ≤
        (Z.pointMultiplicity p : ENNReal) by exact_mod_cast hnat).trans (hcap p)
    have hmass : cap * threshold ≤ packet.mass := (Finset.mem_filter.mp hl).2
    have hvolume := hmass.trans (mass_le_of_pointMultiplicity_le hpacketCap)
    have hdivide := (ENNReal.div_le_iff hcapZero hcapTop).2
      (show cap * threshold ≤ volume packet.union * cap by simpa [mul_comm] using hvolume)
    rw [mul_comm cap, ENNReal.mul_div_cancel_right hcapZero hcapTop] at hdivide
    exact hdivide

end Kakeya.Assouad
end
