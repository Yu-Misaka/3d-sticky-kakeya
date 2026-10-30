import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.DenseGrainNormal
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.DenseCellRefinement
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.GridCubeCover

/-!
# Short global grains made of complete fine cells

The labels retain the original global grain and add a square-root-scale
bin along its rotated y-axis.  Counting these labels and taking their
fibres never changes the supplied tube family or interval.
-/

noncomputable section
open MeasureTheory Set
namespace Kakeya.Assouad
attribute [local instance] Classical.propDecidable

def pureWZ2ShortGrainLabel (slope : ℝ → ℝ) (delta : ℝ)
    (cell : WZ2PaperCellIndex) : (ℤ × ℤ) × ℤ :=
  (pureWZ2GlobalGrainLabel slope delta cell,
    Int.floor (pureWZ2HorizontalRotation
      (slope ((pureWZ2PaperCellCenter delta cell) 2))
      (pureWZ2PaperCellCenter delta cell) 1 / Real.sqrt delta))

theorem pureWZ2_scalar_bin_center_bound {h value : ℝ} (hh : 0 < h) :
    |value - ((Int.floor (value / h) : ℝ) + 1 / 2) * h| ≤ h / 2 := by
  have hlo := Int.floor_le (value / h)
  have hhi := Int.lt_floor_add_one (value / h)
  have hlo' := (le_div_iff₀ hh).1 hlo
  have hhi' := (div_lt_iff₀ hh).1 hhi
  rw [abs_le]
  constructor <;> linarith

theorem pureWZ2_scalar_bins_card_bound
    {Cell : Type*} [DecidableEq Cell] (cells : Finset Cell)
    (value : Cell → ℝ) {h : ℝ} (hh : 0 < h) (hhOne : h ≤ 1)
    (hvalue : ∀ c ∈ cells, |value c| ≤ 2) :
    ((cells.image fun c => Int.floor (value c / h)).card : ℝ) ≤ 6 / h := by
  let bins := cells.image fun c => Int.floor (value c / h)
  let values : Finset ℝ := bins.image fun k : ℤ => (k : ℝ)
  have hcard : values.card = bins.card := Finset.card_image_of_injective _ Int.cast_injective
  by_cases hempty : values = ∅
  · have hb : bins.card = 0 := by rw [← hcard, hempty]; simp
    change (bins.card : ℝ) ≤ _
    calc
      (bins.card : ℝ) = 0 := by exact_mod_cast hb
      _ ≤ 6 / h := div_nonneg (by norm_num) hh.le
  have hnonempty := Finset.nonempty_iff_ne_empty.mpr hempty
  have hrange : ∀ v ∈ values, -2 / h - 1 ≤ v ∧ v ≤ 2 / h := by
    intro v hv
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hk
    have hbounds := abs_le.mp (hvalue c hc)
    have hlow : -2 / h ≤ value c / h := by gcongr; exact hbounds.1
    have hhigh : value c / h ≤ 2 / h := by gcongr; exact hbounds.2
    constructor
    · linarith [Int.lt_floor_add_one (value c / h)]
    · exact (Int.floor_le _).trans hhigh
  have hsep : ∀ v ∈ values, ∀ w ∈ values, v ≠ w → 1 ≤ |v - w| := by
    rintro v hv w hw hne
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hw
    have hij : i ≠ j := by intro h; exact hne (congrArg (fun k : ℤ => (k : ℝ)) h)
    have h := Int.one_le_abs (sub_ne_zero.mpr hij)
    exact_mod_cast h
  have hcount := lemma23_separated_real_finset_card_le (by norm_num : (0 : ℝ) < 1)
    hnonempty hrange hsep
  rw [hcard] at hcount
  change (bins.card : ℝ) ≤ _
  have hcount' : (bins.card : ℝ) ≤ 4 / h + 2 := by
    convert hcount using 1 <;> ring
  have htwo : (2 : ℝ) ≤ 2 / h := (le_div_iff₀ hh).2 (by linarith)
  calc
    (bins.card : ℝ) ≤ 4 / h + 2 := hcount'
    _ ≤ 4 / h + 2 / h := add_le_add le_rfl htwo
    _ = 6 / h := by ring

theorem pureWZ2_short_grain_label_count
    {sigma loss delta a b : ℝ}
    (cfg : PureWZ2C2GrainConfiguration sigma loss delta)
    (Z : WZ1PaperTubeShading cfg.family)
    (hcubical : WZ1PaperIsCubicalShading Z)
    (hsub : PureWZ2PaperIsSubshading Z cfg.shading)
    (hab : a < b) (hslab : ∀ i, Z.carrier i ⊆ horizontalSlab a b) :
    (((wz1PaperActiveCells Z cfg.extremal.delta_pos).image
      (pureWZ2ShortGrainLabel cfg.globalGrains.slope delta)).card : ENNReal) ≤
        ENNReal.ofReal ((b - a) / delta + 2) *
          (24 * Kakeya.realRpowENN delta (-loss) *
            Kakeya.realRpowENN (1 / delta) (1 - sigma)) *
              ENNReal.ofReal (6 / Real.sqrt delta) := by
  let cells := wz1PaperActiveCells Z cfg.extremal.delta_pos
  let longLabels := pureWZ2GlobalGrainLabels cfg.globalGrains.slope delta cells
  let value := fun c => pureWZ2HorizontalRotation
    (cfg.globalGrains.slope ((pureWZ2PaperCellCenter delta c) 2))
    (pureWZ2PaperCellCenter delta c) 1
  let bins := cells.image fun c => Int.floor (value c / Real.sqrt delta)
  have hvalue : ∀ c ∈ cells, |value c| ≤ 2 := by
    intro c hc
    obtain ⟨i, hi⟩ := pureWZ2_activeCellCenter_mem_union cfg.extremal.delta_pos hcubical hc
    exact abs_le.mpr (pureWZ2HorizontalRotation_coord_one_mem_two _
      ((Z.subset_body i hi).2))
  have hbins : (bins.card : ENNReal) ≤ ENNReal.ofReal (6 / Real.sqrt delta) := by
    rw [← ENNReal.ofReal_natCast]
    apply ENNReal.ofReal_mono
    exact pureWZ2_scalar_bins_card_bound cells value (Real.sqrt_pos.mpr cfg.extremal.delta_pos)
      (Real.sqrt_le_one.mpr cfg.extremal.delta_le_one) hvalue
  have hheight := pureWZ2_globalGrainHeights_card_bound cfg.extremal.delta_pos cells
    (fun _ h => h) hab hslab
  have hlong : (longLabels.card : ENNReal) ≤
      ENNReal.ofReal ((b - a) / delta + 2) *
        (24 * Kakeya.realRpowENN delta (-loss) *
          Kakeya.realRpowENN (1 / delta) (1 - sigma)) := by
    have hb := pureWZ2_globalLabels_enncard_le_height_mul_bins
      cfg.globalGrains.slope delta cells _ (by
        intro heightIndex hheightIndex
        obtain ⟨c, hc, hcHeight⟩ := Finset.mem_image.mp hheightIndex
        obtain ⟨i, hi⟩ := pureWZ2_activeCellCenter_mem_union cfg.extremal.delta_pos hcubical hc
        have hbox := (Z.subset_body i hi).2
        have hz : (pureWZ2PaperCellCenter delta c) 2 ∈ Set.Icc (-1 : ℝ) 1 := by
          exact abs_le.mp (hbox.2.2.trans (by norm_num))
        have hzeq : (pureWZ2PaperCellCenter delta c) 2 =
            ((heightIndex : ℝ) + 1 / 2) * delta := by simp [hcHeight]
        rw [hzeq] at hz
        exact pureWZ2_globalBinsAtHeight_card_bound cfg hcubical hsub cells
          (fun _ h => h) heightIndex hz)
    have hh : ((pureWZ2GlobalGrainHeights cells).card : ENNReal) ≤
        ENNReal.ofReal ((b - a) / delta + 2) := by
      rw [← ENNReal.ofReal_natCast]
      exact ENNReal.ofReal_mono hheight
    exact hb.trans (mul_le_mul_right' hh _)
  have hlabels : cells.image (pureWZ2ShortGrainLabel cfg.globalGrains.slope delta) ⊆
      longLabels ×ˢ bins := by
    rintro l hl
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hl
    exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hc,
      Finset.mem_image_of_mem _ hc⟩
  have hcount := Finset.card_le_card hlabels
  rw [Finset.card_product] at hcount
  have henn : ((cells.image (pureWZ2ShortGrainLabel cfg.globalGrains.slope delta)).card :
      ENNReal) ≤ (longLabels.card : ENNReal) * bins.card := by exact_mod_cast hcount
  exact henn.trans (mul_le_mul' hlong hbins)

/-- Every nonempty short-label packet has a literal thin-tube geometry.
Its original slope stays close to the packet frame on every retained cell. -/
theorem pureWZ2_short_grain_packet_geometry
    {sigma loss delta : ℝ}
    (cfg : PureWZ2C2GrainConfiguration sigma loss delta)
    (Z : WZ1PaperTubeShading cfg.family)
    (hcubical : WZ1PaperIsCubicalShading Z)
    (hsub : PureWZ2PaperIsSubshading Z cfg.shading)
    (label : (ℤ × ℤ) × ℤ)
    (hpacket : (wz2RefinedShading Z
      ((wz1PaperActiveCells Z cfg.extremal.delta_pos).filter fun c =>
        pureWZ2ShortGrainLabel cfg.globalGrains.slope delta c = label)).union.Nonempty) :
    ∃ slope x y z : ℝ, |slope| ≤ 1 ∧
      (wz2RefinedShading Z
        ((wz1PaperActiveCells Z cfg.extremal.delta_pos).filter fun c =>
          pureWZ2ShortGrainLabel cfg.globalGrains.slope delta c = label)).union ⊆
        pureWZ2ShortGlobalGrain delta slope x y z ∧
      ∀ p ∈ (wz2RefinedShading Z
        ((wz1PaperActiveCells Z cfg.extremal.delta_pos).filter fun c =>
          pureWZ2ShortGrainLabel cfg.globalGrains.slope delta c = label)).union,
        |cfg.globalGrains.slope (p 2) - slope| ≤ delta / 2 := by
  let cells := (wz1PaperActiveCells Z cfg.extremal.delta_pos).filter fun c =>
    pureWZ2ShortGrainLabel cfg.globalGrains.slope delta c = label
  let packet := wz2RefinedShading Z cells
  have hunion : packet.union = ⋃ c ∈ cells, wz1PaperGridCube delta c :=
    wz2RefinedShading_union_eq hcubical cfg.extremal.delta_pos
      (fun _ h => (Finset.mem_filter.mp h).1)
  obtain ⟨p₀, hp₀⟩ := hpacket
  rw [hunion] at hp₀
  obtain ⟨c₀, hc₀, _⟩ := Set.mem_iUnion₂.mp hp₀
  let anchor := pureWZ2PaperCellCenter delta c₀
  let slope := cfg.globalGrains.slope (anchor 2)
  let R := pureWZ2HorizontalRotation slope
  have hanchor : anchor ∈ Z.union := pureWZ2_activeCellCenter_mem_union
    cfg.extremal.delta_pos hcubical (Finset.mem_filter.mp hc₀).1
  obtain ⟨i₀, hi₀⟩ := hanchor
  have hanchorBox := (Z.subset_body i₀ hi₀).2
  have hanchorHeight : anchor 2 ∈ Set.Icc (-1 : ℝ) 1 := by
    simpa [Kakeya.Streamlined.axisBox, abs_le] using hanchorBox.2.2
  have hslope : |slope| ≤ 1 := (cfg.globalGrains.slope_normalized _ hanchorHeight).1
  have hden : 1 ≤ pureWZ2HorizontalNorm slope := by
    nlinarith [pureWZ2HorizontalNorm_sq slope,
      pureWZ2HorizontalNorm_pos slope, sq_nonneg slope]
  have hsame : ∀ c ∈ cells,
      pureWZ2GlobalGrainLabel cfg.globalGrains.slope delta c =
        pureWZ2GlobalGrainLabel cfg.globalGrains.slope delta c₀ := by
    intro c hc
    exact congrArg Prod.fst ((Finset.mem_filter.mp hc).2.trans (Finset.mem_filter.mp hc₀).2.symm)
  have hheight : ∀ c ∈ cells, (pureWZ2PaperCellCenter delta c) 2 = anchor 2 := by
    intro c hc
    exact sub_eq_zero.mp (abs_eq_zero.mp
      (pureWZ2_cellCenters_same_label cfg.extremal.delta_pos cfg.globalGrains.slope (hsame c hc)).1)
  refine ⟨slope, R anchor 0, ((label.2 : ℝ) + 1 / 2) * Real.sqrt delta,
    anchor 2, hslope, ?_, ?_⟩
  · intro p hp
    rw [hunion] at hp
    obtain ⟨c, hc, hpc⟩ := Set.mem_iUnion₂.mp hp
    have hgrain := pureWZ2_same_label_cell_subset_globalGrain cfg.extremal.delta_pos
      cfg.globalGrains.slope cfg.globalGrains.slope_normalized hanchorHeight (hsame c hc) hpc
    have hxraw : |(p 0 + slope * p 1) - (anchor 0 + slope * anchor 1)| ≤ 4 * delta := by
      simpa [pureWZ2GlobalGrainWithConstant, globalGrainDirection, PiLp.inner_apply,
        Fin.sum_univ_succ, slope, anchor] using hgrain.2
    have hx : |R p 0 - R anchor 0| ≤ 4 * delta := by
      dsimp only [R]
      rw [pureWZ2HorizontalRotation_coord_zero, pureWZ2HorizontalRotation_coord_zero,
        ← sub_div, abs_div, abs_of_pos (pureWZ2HorizontalNorm_pos slope),
        div_le_iff₀ (pureWZ2HorizontalNorm_pos slope)]
      nlinarith [cfg.extremal.delta_pos]
    have hybin : Int.floor (R (pureWZ2PaperCellCenter delta c) 1 / Real.sqrt delta) = label.2 := by
      have h := congrArg Prod.snd (Finset.mem_filter.mp hc).2
      simpa [pureWZ2ShortGrainLabel, hheight c hc, slope, R] using h
    have hycenter := pureWZ2_scalar_bin_center_bound
      (value := R (pureWZ2PaperCellCenter delta c) 1)
      (Real.sqrt_pos.mpr cfg.extremal.delta_pos)
    rw [hybin] at hycenter
    have hdist : dist p (pureWZ2PaperCellCenter delta c) ≤ 2 * delta := by
      have hd := dist_le_sqrt3_of_mem_wz1PaperGridCube cfg.extremal.delta_pos hpc
        (pureWZ2PaperCellCenter_mem cfg.extremal.delta_pos c)
      have hthree : Real.sqrt 3 ≤ 2 := by
        nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg 3]
      exact hd.trans (by nlinarith [cfg.extremal.delta_pos])
    have hyclose : |R p 1 - R (pureWZ2PaperCellCenter delta c) 1| ≤ 2 * delta := by
      have h := PiLp.norm_apply_le (R p - R (pureWZ2PaperCellCenter delta c)) (1 : Fin 3)
      have heq : ‖R p - R (pureWZ2PaperCellCenter delta c)‖ =
          dist p (pureWZ2PaperCellCenter delta c) := by rw [← dist_eq_norm, R.dist_map]
      rw [heq] at h
      have h' : |R p 1 - R (pureWZ2PaperCellCenter delta c) 1| ≤
          dist p (pureWZ2PaperCellCenter delta c) := by simpa [Real.norm_eq_abs] using h
      exact h'.trans hdist
    refine ⟨hx, ?_, hgrain.1⟩
    have h := abs_sub_le (R p 1) (R (pureWZ2PaperCellCenter delta c) 1)
      (((label.2 : ℝ) + 1 / 2) * Real.sqrt delta)
    linarith
  · intro p hp
    have hZ : p ∈ Z.union := by
      obtain ⟨i, hi⟩ := hp
      exact ⟨i, hi.1⟩
    obtain ⟨i, hi⟩ := hZ
    have hbox := (Z.subset_body i hi).2
    have hpheight : p 2 ∈ Set.Icc (-1 : ℝ) 1 := by
      simpa [Kakeya.Streamlined.axisBox, abs_le] using hbox.2.2
    rw [hunion] at hp
    obtain ⟨c, hc, hpc⟩ := Set.mem_iUnion₂.mp hp
    have hclose := pureWZ2_point_close_to_cellCenter cfg.extremal.delta_pos hpc 2
    rw [hheight c hc] at hclose
    have hlip := cfg.globalGrains.slope_lipschitzOn.norm_sub_le hpheight hanchorHeight
    have hlip' : |cfg.globalGrains.slope (p 2) - slope| ≤ |p 2 - anchor 2| := by
      simpa [Real.norm_eq_abs, slope] using hlip
    exact hlip'.trans hclose

end Kakeya.Assouad
end
