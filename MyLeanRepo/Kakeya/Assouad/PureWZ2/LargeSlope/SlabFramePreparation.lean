import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.ShortGrainCells
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.FrameNormalCompatibilityCore

/-!
# Frame preparation after an arbitrary slab is supplied

The short-grain selection retains half of the slab's incidence mass on the
original family.  Its frame certificate follows from local AD.  Only the
normalized slab mass and the fine multiplicity cap enter the scalar budget.
-/

noncomputable section
open MeasureTheory Set
namespace Kakeya.Assouad
attribute [local instance] Classical.propDecidable

private theorem short_grain_budget_identity
    {delta L sigma loss capLoss eta : ℝ} (hdelta : 0 < delta) :
    2 * (3 * L / delta) *
        (24 * Real.rpow delta (-loss) * Real.rpow (1 / delta) (1 - sigma)) *
        (6 / Real.sqrt delta) *
        (Real.rpow delta (2 - sigma - capLoss) *
          (144 * Real.rpow delta eta * delta ^ 2 * Real.sqrt delta)) =
      124416 * Real.rpow delta (eta - loss - capLoss + 2) * L := by
  have hinv : Real.rpow (1 / delta) (1 - sigma) = Real.rpow delta (sigma - 1) := by
    change (1 / delta) ^ (1 - sigma) = delta ^ (sigma - 1)
    rw [one_div, Real.inv_rpow hdelta.le, ← Real.rpow_neg hdelta.le]
    congr 1
    ring
  have hp : Real.rpow delta (-loss) * Real.rpow delta (sigma - 1) *
      Real.rpow delta (2 - sigma - capLoss) * Real.rpow delta eta * delta =
      Real.rpow delta (eta - loss - capLoss + 2) := by
    change delta ^ (-loss) * delta ^ (sigma - 1) * delta ^ (2 - sigma - capLoss) *
      delta ^ eta * delta = delta ^ (eta - loss - capLoss + 2)
    conv_lhs => arg 2; rw [← Real.rpow_one delta]
    rw [← Real.rpow_add hdelta, ← Real.rpow_add hdelta,
      ← Real.rpow_add hdelta, ← Real.rpow_add hdelta]
    congr 1
    ring
  rw [hinv]
  calc
    _ = 124416 * (Real.rpow delta (-loss) * Real.rpow delta (sigma - 1) *
        Real.rpow delta (2 - sigma - capLoss) * Real.rpow delta eta * delta) * L := by
      field_simp [hdelta.ne', (Real.sqrt_pos.mpr hdelta).ne']
      <;> ring
    _ = _ := by rw [hp]

/-- A same-family refinement of any supplied whole-cell slab acquires the
normal certificate.  It retains at least half of that slab's mass. -/
theorem pureWZ2_prescribed_slab_frame_preparation
    (sigma loss capLoss massLoss eta : ℝ)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (heta : 0 < eta) (hloss : loss < eta) (hgap : 6 * eta < sigma)
    (hmassGap : massLoss < eta - loss - capLoss) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
        ∀ cfg : PureWZ2C2GrainConfiguration sigma loss delta,
        ∀ Z : WZ1PaperTubeShading cfg.family,
          WZ1PaperIsCubicalShading Z → PureWZ2PaperIsSubshading Z cfg.shading →
        ∀ a b : ℝ, a < b → delta ≤ b - a →
          (∀ i, Z.carrier i ⊆ horizontalSlab a b) →
          Kakeya.realRpowENN delta (massLoss + 2) * cfg.family.enncard *
            ENNReal.ofReal (b - a) ≤ Z.mass →
          (∀ p, (Z.pointMultiplicity p : ENNReal) ≤
            Kakeya.realRpowENN delta (2 - sigma - capLoss) * cfg.family.enncard) →
          ∃ refined : WZ1PaperTubeShading cfg.family,
            PureWZ2PaperIsSubshading refined Z ∧ WZ1PaperIsCubicalShading refined ∧
            Z.mass ≤ 2 * refined.mass ∧
            PureWZ2FrameNormalCompatibilityOn cfg refined.union := by
  obtain ⟨normalScale, hnormalScale, _, normalBound⟩ :=
    pureWZ2_dense_short_global_grain_normal sigma loss eta hsigma hsigmaOne heta hloss hgap
  obtain ⟨massScale, hmassScale, _, massBound⟩ :=
    exists_delta_mul_rpow_le_rpow 124416 (by norm_num)
      (show massLoss + 2 < eta - loss - capLoss + 2 by linarith)
  let delta₀ := min (1 / 256) (min normalScale massScale)
  refine ⟨delta₀, by dsimp [delta₀]; positivity,
    (min_le_left _ _).trans (by norm_num), ?_⟩
  intro delta hdelta hcut cfg Z hcubical hsub a b hab hlength hslab hmass hcap
  have htiny : delta ≤ 1 / 256 := hcut.trans (by simp [delta₀])
  have hnormalCut : delta ≤ normalScale := hcut.trans (by simp [delta₀])
  have hmassCut : delta ≤ massScale := hcut.trans (by simp [delta₀])
  let label := pureWZ2ShortGrainLabel cfg.globalGrains.slope delta
  let cells := wz1PaperActiveCells Z hdelta
  let cap := Kakeya.realRpowENN delta (2 - sigma - capLoss) * cfg.family.enncard
  let threshold := ENNReal.ofReal
    (144 * Real.rpow delta eta * delta ^ 2 * Real.sqrt delta)
  have hcapZero : cap ≠ 0 := by
    apply mul_ne_zero
    · exact (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hdelta _)).ne'
    · change (cfg.family.card : ENNReal) ≠ 0
      exact_mod_cast cfg.extremal.nonempty.ne'
  have hcapTop : cap ≠ ⊤ := by
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by simp [Kakeya.Streamlined.TubeFamily.enncard])
  have hthreshold : 0 < threshold := ENNReal.ofReal_pos.mpr (by
    dsimp [threshold]
    positivity)
  have hcount := pureWZ2_short_grain_label_count cfg Z hcubical hsub hab hslab
  have hheight : (b - a) / delta + 2 ≤ 3 * (b - a) / delta := by
    have h : (1 : ℝ) ≤ (b - a) / delta := (le_div_iff₀ hdelta).2 (by simpa using hlength)
    calc
      (b - a) / delta + 2 ≤ (b - a) / delta + 2 * ((b - a) / delta) := by linarith
      _ = _ := by ring
  have hscalarReal :
      2 * (3 * (b - a) / delta) *
          (24 * Real.rpow delta (-loss) * Real.rpow (1 / delta) (1 - sigma)) *
          (6 / Real.sqrt delta) *
          (Real.rpow delta (2 - sigma - capLoss) *
            (144 * Real.rpow delta eta * delta ^ 2 * Real.sqrt delta)) ≤
        Real.rpow delta (massLoss + 2) * (b - a) := by
    rw [short_grain_budget_identity hdelta]
    exact mul_le_mul_of_nonneg_right (massBound delta hdelta hmassCut) (sub_pos.mpr hab).le
  have hscalar :
      2 * ENNReal.ofReal (3 * (b - a) / delta) *
          (24 * Kakeya.realRpowENN delta (-loss) *
            Kakeya.realRpowENN (1 / delta) (1 - sigma)) *
          ENNReal.ofReal (6 / Real.sqrt delta) *
          (Kakeya.realRpowENN delta (2 - sigma - capLoss) * threshold) ≤
        Kakeya.realRpowENN delta (massLoss + 2) * ENNReal.ofReal (b - a) := by
    have hp₁ : 0 ≤ Real.rpow delta (-loss) := Real.rpow_nonneg hdelta.le _
    have hp₂ : 0 ≤ Real.rpow (1 / delta) (1 - sigma) := Real.rpow_nonneg (by positivity) _
    have hp₃ : 0 ≤ Real.rpow delta (2 - sigma - capLoss) := Real.rpow_nonneg hdelta.le _
    have hp₄ : 0 ≤ Real.rpow delta eta := Real.rpow_nonneg hdelta.le _
    have hp₅ : 0 ≤ Real.rpow delta (massLoss + 2) := Real.rpow_nonneg hdelta.le _
    have hba : 0 ≤ b - a := (sub_pos.mpr hab).le
    have h := ENNReal.ofReal_mono hscalarReal
    simpa (disch := positivity) only [Kakeya.realRpowENN, threshold,
      ENNReal.ofReal_mul, ENNReal.ofReal_ofNat] using h
  have hbudget : 2 * ((cells.image label).card : ENNReal) * (cap * threshold) ≤ Z.mass := by
    calc
      _ ≤ 2 * (ENNReal.ofReal (3 * (b - a) / delta) *
          (24 * Kakeya.realRpowENN delta (-loss) *
            Kakeya.realRpowENN (1 / delta) (1 - sigma)) *
          ENNReal.ofReal (6 / Real.sqrt delta)) * (cap * threshold) := by
        gcongr
        exact hcount.trans (by gcongr)
      _ = (2 * ENNReal.ofReal (3 * (b - a) / delta) *
          (24 * Kakeya.realRpowENN delta (-loss) *
            Kakeya.realRpowENN (1 / delta) (1 - sigma)) *
          ENNReal.ofReal (6 / Real.sqrt delta) *
          (Kakeya.realRpowENN delta (2 - sigma - capLoss) * threshold)) *
          cfg.family.enncard := by dsimp [cap]; ring
      _ ≤ (Kakeya.realRpowENN delta (massLoss + 2) * ENNReal.ofReal (b - a)) *
          cfg.family.enncard := mul_le_mul_right' hscalar _
      _ = Kakeya.realRpowENN delta (massLoss + 2) * cfg.family.enncard *
          ENNReal.ofReal (b - a) := by ring
      _ ≤ Z.mass := hmass
  obtain ⟨kept, _, hretained, hdense⟩ := pureWZ2_dense_cell_label_refinement
    Z hdelta hcubical label cap threshold hcapZero hcapTop ENNReal.ofReal_ne_top hcap hbudget
  let refined := wz2RefinedShading Z (cells.filter fun c => label c ∈ kept)
  refine ⟨refined, fun i => Set.inter_subset_left, wz2RefinedShading_cubical hcubical,
    hretained, ?_⟩
  intro frameSlope p hp hframe
  obtain ⟨i, hi⟩ := hp
  obtain ⟨c, hc, hpc⟩ := Set.mem_iUnion₂.mp hi.2
  have hckept : label c ∈ kept := (Finset.mem_filter.mp hc).2
  let packet := wz2RefinedShading Z (cells.filter fun c' => label c' = label c)
  have hppacket : p.1 ∈ packet.union := by
    exact ⟨i, hi.1, Set.mem_iUnion₂.mpr
      ⟨c, Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hc).1, rfl⟩, hpc⟩⟩
  obtain ⟨slope, x, y, z, hslope, hgeometry, hslopeClose⟩ :=
    pureWZ2_short_grain_packet_geometry cfg Z hcubical hsub (label c) ⟨p.1, hppacket⟩
  have hpacketSub : packet.union ⊆ cfg.shading.union := by
    rintro q ⟨j, hj⟩
    exact ⟨j, hsub j hj.1⟩
  have hclose : |slope - frameSlope| ≤ 1 / 25 := by
    have hlocal : |slope - cfg.globalGrains.slope (p.1 2)| ≤ delta / 2 := by
      simpa only [abs_sub_comm] using hslopeClose p.1 hppacket
    calc
      _ ≤ |slope - cfg.globalGrains.slope (p.1 2)| +
        |cfg.globalGrains.slope (p.1 2) - frameSlope| := abs_sub_le _ _ _
      _ ≤ delta / 2 + 1 / 50 := add_le_add hlocal hframe
      _ ≤ 1 / 25 := by linarith
  have hnormal := normalBound delta hdelta hnormalCut cfg slope x y z hslope
    packet.union (measurableSet_shading_union packet) hpacketSub hgeometry
    (hdense (label c) hckept) p hppacket frameSlope hclose
  exact (by norm_num : (1 / 16 : ℝ) ≤ 1 / 2).trans hnormal

end Kakeya.Assouad
end
