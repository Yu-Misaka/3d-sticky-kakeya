import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.CroppedRefinementData
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.GridCubeCover
import MyLeanRepo.Kakeya.Assouad.PropStickyExactCellBalancingHelpers
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperFinalFineExactBalancingHelpers
import MyLeanRepo.Kakeya.Assouad.WZ1.Proposition3_2PaperCubicalRefinement

/-!
# Whole-cell preparation of an arbitrary prescribed slab

Retain all occupied delta-cells meeting the specified slab. This retains
every original slab incidence, stays in a slab enlarged by delta at each
end, and enlarges a spatial cover's radius by at most 2*delta. Each retained
point has exactly the same tube incidences as a point in the original slab,
so bounds on point multiplicity inside the prescribed slab survive the hull.
No mass selection in a different height layer is used.
-/

noncomputable section
open MeasureTheory Set
namespace Kakeya.Assouad

def pureWZ2PrescribedSlabCells {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta} (Y : WZ1PaperTubeShading F)
    (hdelta : 0 < delta) (a b : ℝ) : Finset (ℤ × ℤ × ℤ) := by
  classical
  exact (wz1PaperActiveCells Y hdelta).filter fun cell =>
    (wz1PaperGridCube delta cell ∩ horizontalSlab a b).Nonempty

def pureWZ2PrescribedSlabHull {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta} (Y : WZ1PaperTubeShading F)
    (hdelta : 0 < delta) (a b : ℝ) : WZ1PaperTubeShading F :=
  wz2RefinedShading Y (pureWZ2PrescribedSlabCells Y hdelta a b)

theorem pureWZ2PrescribedSlabHull_subshading {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta} (Y : WZ1PaperTubeShading F)
    (hdelta : 0 < delta) (a b : ℝ) (i : Fin F.card) :
    (pureWZ2PrescribedSlabHull Y hdelta a b).carrier i ⊆ Y.carrier i :=
  wz2RefinedShading_subshading i

theorem pureWZ2PrescribedSlabHull_cubical {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta} (Y : WZ1PaperTubeShading F)
    (hdelta : 0 < delta) (a b : ℝ) (hY : WZ1PaperIsCubicalShading Y) :
    WZ1PaperIsCubicalShading (pureWZ2PrescribedSlabHull Y hdelta a b) :=
  wz2RefinedShading_cubical hY

theorem pureWZ2PrescribedSlabHull_contains {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta} (Y : WZ1PaperTubeShading F)
    (hdelta : 0 < delta) (a b : ℝ) (hY : WZ1PaperIsCubicalShading Y)
    (i : Fin F.card) :
    Y.carrier i ∩ horizontalSlab a b ⊆
      (pureWZ2PrescribedSlabHull Y hdelta a b).carrier i := by
  classical
  rintro p ⟨hp, hslab⟩
  have hunion : p ∈ Y.union := ⟨i, hp⟩
  rw [hY.union_eq_activeCells hdelta] at hunion
  obtain ⟨cell, hcell, hpCell⟩ := Set.mem_iUnion₂.mp hunion
  refine ⟨hp, Set.mem_iUnion₂.mpr ⟨cell, ?_, hpCell⟩⟩
  exact Finset.mem_filter.mpr ⟨hcell, ⟨p, hpCell, hslab⟩⟩

theorem pureWZ2PrescribedSlabHull_mass {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta} (Y : WZ1PaperTubeShading F)
    (hdelta : 0 < delta) (a b : ℝ) (hY : WZ1PaperIsCubicalShading Y) :
    paperShadedMassInSlab Y a b ≤ (pureWZ2PrescribedSlabHull Y hdelta a b).mass := by
  apply Finset.sum_le_sum
  intro i _
  exact measure_mono (pureWZ2PrescribedSlabHull_contains Y hdelta a b hY i)

/-- Every retained point has the incidences of a point in the prescribed slab. -/
theorem pureWZ2PrescribedSlabHull_witness {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta} (Y : WZ1PaperTubeShading F)
    (hdelta : 0 < delta) (a b : ℝ) (hY : WZ1PaperIsCubicalShading Y)
    {p : Point3} (hp : p ∈ (pureWZ2PrescribedSlabHull Y hdelta a b).union) :
    ∃ q ∈ Y.union ∩ horizontalSlab a b,
      dist p q ≤ 2 * delta ∧ |p 2 - q 2| ≤ delta ∧
      ∀ i, p ∈ (pureWZ2PrescribedSlabHull Y hdelta a b).carrier i ↔ q ∈ Y.carrier i := by
  classical
  obtain ⟨index, hpSource, hpHull⟩ := hp
  obtain ⟨cell, hcell, hpCell⟩ := Set.mem_iUnion₂.mp hpHull
  obtain ⟨hactive, q, hqCell, hqSlab⟩ := Finset.mem_filter.mp hcell
  have hpIndex := (mem_wz1PaperGridCube delta cell p).mp hpCell
  have hqIndex := (mem_wz1PaperGridCube delta cell q).mp hqCell
  have hsame := hpIndex.trans hqIndex.symm
  have hqSource : q ∈ Y.carrier index :=
    (hY.carrier_mem_iff_of_same_cell index hsame).mp hpSource
  have hdistance : dist p q ≤ 2 * delta := by
    have hroot : Real.sqrt 3 ≤ 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg 3]
    exact (dist_le_sqrt3_of_mem_wz1PaperGridCube hdelta hpCell hqCell).trans (by nlinarith)
  have hheight : |p 2 - q 2| ≤ delta := by
    rw [wz1PaperGridCube_eq_Ico hdelta cell] at hpCell hqCell
    exact abs_le.mpr ⟨by linarith [hpCell.2.2.2.2.1, hqCell.2.2.2.2.2],
      by linarith [hpCell.2.2.2.2.2, hqCell.2.2.2.2.1]⟩
  refine ⟨q, ⟨⟨index, hqSource⟩, hqSlab⟩, hdistance, hheight, ?_⟩
  intro i
  constructor
  · exact fun hi => (hY.carrier_mem_iff_of_same_cell i hsame).mp hi.1
  · intro hi
    refine ⟨(hY.carrier_mem_iff_of_same_cell i hsame).mpr hi, ?_⟩
    exact Set.mem_iUnion₂.mpr ⟨cell, hcell,
      (mem_wz1PaperGridCube delta cell p).mpr hpIndex⟩

theorem pureWZ2PrescribedSlabHull_cover {delta r : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta} (Y : WZ1PaperTubeShading F)
    (hdelta : 0 < delta) (a b : ℝ) (hY : WZ1PaperIsCubicalShading Y)
    {N : ENNReal} (hcover : CanCoverByBalls (Y.union ∩ horizontalSlab a b) r N) :
    CanCoverByBalls (pureWZ2PrescribedSlabHull Y hdelta a b).union (r + 2 * delta) N := by
  obtain ⟨centers, hcard, hcover⟩ := hcover
  refine ⟨centers, hcard, ?_⟩
  intro p hp
  obtain ⟨q, hq, hpq, _, _⟩ := pureWZ2PrescribedSlabHull_witness Y hdelta a b hY hp
  obtain ⟨c, hc, hqc⟩ := hcover q hq
  refine ⟨c, hc, Metric.mem_closedBall.mpr ?_⟩
  calc
    dist p c ≤ dist p q + dist q c := dist_triangle _ _ _
    _ ≤ 2 * delta + r := add_le_add hpq hqc
    _ = r + 2 * delta := by ring

theorem pureWZ2PrescribedSlabHull_multiplicity {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta} (Y : WZ1PaperTubeShading F)
    (hdelta : 0 < delta) (a b : ℝ) (hY : WZ1PaperIsCubicalShading Y)
    {M : ENNReal}
    (hcap : ∀ p ∈ Y.union ∩ horizontalSlab a b, (Y.pointMultiplicity p : ENNReal) ≤ M)
    (p : Point3) :
    ((pureWZ2PrescribedSlabHull Y hdelta a b).pointMultiplicity p : ENNReal) ≤ M := by
  classical
  by_cases hp : p ∈ (pureWZ2PrescribedSlabHull Y hdelta a b).union
  · obtain ⟨q, hq, _, _, hincidence⟩ := pureWZ2PrescribedSlabHull_witness Y hdelta a b hY hp
    have hmult : (pureWZ2PrescribedSlabHull Y hdelta a b).pointMultiplicity p =
        Y.pointMultiplicity q := by
      unfold Kakeya.Streamlined.Shading.pointMultiplicity
      congr 1
      exact Finset.filter_congr (fun i _ => hincidence i)
    rw [hmult]
    exact hcap q hq
  · have hzero : (pureWZ2PrescribedSlabHull Y hdelta a b).pointMultiplicity p = 0 := by
      apply Finset.card_eq_zero.mpr
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i hi
      exact hp ⟨i, (Finset.mem_filter.mp hi).2⟩
    rw [hzero, Nat.cast_zero]
    positivity

/-- A padded interval can be placed inside the original height window. -/
def pureWZ2PrescribedSlabLeft (delta a b : ℝ) : ℝ :=
  max (-1) (min (a - delta) (1 - (b - a + 2 * delta)))

theorem pureWZ2PrescribedSlabHull_height {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta} (Y : WZ1PaperTubeShading F)
    (hdelta : 0 < delta) {a b : ℝ} (ha : -1 ≤ a) (hb : b ≤ 1)
    (hwidth : b - a + 2 * delta ≤ 2) (hY : WZ1PaperIsCubicalShading Y) :
    let left := pureWZ2PrescribedSlabLeft delta a b;
    -1 ≤ left ∧ left + (b - a + 2 * delta) ≤ 1 ∧
      left ≤ a ∧ b ≤ left + (b - a + 2 * delta) ∧
      ∀ i, (pureWZ2PrescribedSlabHull Y hdelta a b).carrier i ⊆
        horizontalSlab left (left + (b - a + 2 * delta)) := by
  dsimp only []
  let R := b - a + 2 * delta
  let left := pureWZ2PrescribedSlabLeft delta a b
  have hleftLower : -1 ≤ left := le_max_left _ _
  have hleftUpper : left ≤ 1 - R := by
    exact max_le (by dsimp [R]; linarith) (min_le_right _ _)
  have hleftA : left ≤ a := max_le ha ((min_le_left _ _).trans (by linarith))
  have hrightB : b ≤ left + R := by
    have h : b - R ≤ min (a - delta) (1 - R) :=
      le_min (by dsimp [R]; linarith) (by linarith)
    have h' : b - R ≤ left := h.trans (le_max_right (-1) _)
    linarith
  refine ⟨hleftLower, by linarith, hleftA, hrightB, ?_⟩
  intro i p hp
  obtain ⟨q, hq, _, hheight, _⟩ :=
    pureWZ2PrescribedSlabHull_witness Y hdelta a b hY ⟨i, hp⟩
  have hpAmbient : -1 ≤ p 2 ∧ p 2 ≤ 1 := by
    have h := (Y.subset_body i hp.1).2
    simpa [Kakeya.Streamlined.axisBox, abs_le] using h.2.2
  have hpLow : a - delta ≤ p 2 := by
    have hqz : a ≤ q 2 ∧ q 2 ≤ b := hq.2
    linarith [abs_le.mp hheight]
  have hpHigh : p 2 ≤ b + delta := by
    have hqz : a ≤ q 2 ∧ q 2 ≤ b := hq.2
    linarith [abs_le.mp hheight]
  constructor
  · exact max_le hpAmbient.1 ((min_le_left _ _).trans hpLow)
  · have h : p 2 - R ≤ min (a - delta) (1 - R) :=
      le_min (by dsimp [R]; linarith) (by linarith [hpAmbient.2])
    have h' : p 2 - R ≤ left := h.trans (le_max_right (-1) _)
    linarith

end Kakeya.Assouad
end
