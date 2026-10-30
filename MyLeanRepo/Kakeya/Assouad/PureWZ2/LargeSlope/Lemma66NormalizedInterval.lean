import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.Lemma66PrescribedInterval
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.SlabFramePreparation

/-!
# Lemma 6.6 on any supplied configuration with normalized slab mass

The configuration and interval are arbitrary.  Whole-cell preparation and
the frame certificate are proved after receiving that interval, retaining
its mass on the same tube family.  The only extra quantitative premises
left here are normalized slab mass and the fine multiplicity cap.

This is not the printed absolute-mass version of Lemma 6.6.
-/

noncomputable section
open MeasureTheory Set
namespace Kakeya.Assouad
attribute [local instance] Classical.propDecidable

theorem pure_wz2_lemma66_normalized_interval
    (sigma epsilon eta : ℝ)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hepsilon : 0 < epsilon) (hepsilonHalf : epsilon ≤ 1 / 2)
    (heta : 0 < eta) (hbudget : 2000 * eta ≤ epsilon * sigma ^ 2) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
        ∀ cfg : PureWZ2C2GrainConfiguration sigma (eta / 8) delta,
          ∀ f : SlopeFunction,
            (∀ z ∈ Set.Icc (-1 : ℝ) 1, f z = cfg.globalGrains.slope z) →
            f.IsNormalized →
            ∀ a b : ℝ, -1 ≤ a → a < b → b ≤ 1 →
              Real.rpow delta (1 / 2) ≤ b - a → b - a ≤ Real.rpow delta epsilon →
              ENNReal.ofReal (Real.pi / 4) * Kakeya.realRpowENN delta (eta / 16 + 2) *
                  cfg.family.enncard * ENNReal.ofReal (b - a) ≤
                paperShadedMassInSlab cfg.shading a b →
              CanCoverByBalls (cfg.shading.union ∩ horizontalSlab a b) (b - a)
                (Kakeya.realRpowENN delta (-(eta / 16)) *
                  Kakeya.realRpowENN (b - a) (-2 + sigma)) →
              (∀ p ∈ cfg.shading.union ∩ horizontalSlab a b,
                (cfg.shading.pointMultiplicity p : ENNReal) ≤
                  Kakeya.realRpowENN delta (2 - sigma - eta / 8192) * cfg.family.enncard) →
              ∀ z ∈ Set.Icc a b, b - a ≤ |deriv f z| := by
  have hsigmaSq : sigma ^ 2 < sigma := by nlinarith
  have hproduct : epsilon * sigma ^ 2 ≤ sigma / 2 := by
    calc
      epsilon * sigma ^ 2 ≤ (1 / 2) * sigma ^ 2 := by gcongr
      _ ≤ sigma / 2 := by linarith
  have hnormalGap : 6 * (eta / 2) < sigma := by linarith
  have hetaOne : eta ≤ 1 := by linarith
  obtain ⟨preparedScale, hpreparedScale, hpreparedOne, prepared⟩ :=
    pure_wz2_lemma66_prepared_interval_on sigma (epsilon / 2) eta hsigma hsigmaOne
      (by positivity) (by linarith) heta (by nlinarith)
  obtain ⟨frameScale, hframeScale, _, framePrepare⟩ :=
    pureWZ2_prescribed_slab_frame_preparation sigma (eta / 8) (eta / 8192)
      (3 * eta / 32) (eta / 2) hsigma hsigmaOne (by positivity) (by linarith)
      hnormalGap (by linarith)
  obtain ⟨massScale, hmassScale, _, massAbsorb⟩ :=
    exists_delta_mul_rpow_le_rpow (12 / Real.pi) (by positivity)
      (show eta / 16 + 2 < 3 * eta / 32 + 2 by linarith)
  obtain ⟨retainedScale, hretainedScale, _, retainedAbsorb⟩ :=
    exists_delta_mul_rpow_le_rpow (Real.pi / 2) (by positivity)
      (show 3 * eta / 32 + 2 < eta / 8 + 2 by linarith)
  obtain ⟨coverScale, hcoverScale, _, coverAbsorb⟩ :=
    exists_delta_mul_rpow_le_rpow 9 (by norm_num)
      (show -(eta / 8) < -(eta / 16) by linarith)
  obtain ⟨widthScale, hwidthScale, _, widthAbsorb⟩ :=
    exists_delta_mul_rpow_le_rpow 3 (by norm_num)
      (show epsilon / 2 < epsilon by linarith)
  let delta₀ := min preparedScale (min frameScale
    (min massScale (min retainedScale (min coverScale widthScale))))
  refine ⟨delta₀, by dsimp [delta₀]; positivity,
    (min_le_left _ _).trans hpreparedOne, ?_⟩
  intro delta hdelta hcut cfg f hf hnormalized a b ha hab hb hlower hupper hmass hcover hcap
  have hprepared : delta ≤ preparedScale := hcut.trans (by simp [delta₀])
  have hframeCut : delta ≤ frameScale := hcut.trans (by simp [delta₀])
  have hmassCut : delta ≤ massScale := hcut.trans (by simp [delta₀])
  have hretainedCut : delta ≤ retainedScale := hcut.trans (by simp [delta₀])
  have hcoverCut : delta ≤ coverScale := hcut.trans (by simp [delta₀])
  have hwidthCut : delta ≤ widthScale := hcut.trans (by simp [delta₀])
  have hdeltaOne : delta ≤ 1 := hprepared.trans hpreparedOne
  have hdeltaRho : delta ≤ b - a := by
    calc
      delta = Real.rpow delta 1 := (Real.rpow_one _).symm
      _ ≤ Real.rpow delta (1 / 2) :=
        Real.rpow_le_rpow_of_exponent_ge hdelta hdeltaOne (by norm_num)
      _ ≤ _ := hlower
  let R := b - a + 2 * delta
  have hR : 0 < R := by dsimp [R]; linarith
  have hRle : R ≤ 3 * (b - a) := by dsimp [R]; linarith
  have hRpower : R ≤ Real.rpow delta (epsilon / 2) := by
    exact hRle.trans ((mul_le_mul_of_nonneg_left hupper (by norm_num)).trans
      (widthAbsorb delta hdelta hwidthCut))
  have hROne : R ≤ 1 := hRpower.trans
    (Real.rpow_le_one hdelta.le hdeltaOne (by positivity))
  let scale : WZ2PaperRequestedScale delta := ⟨R, by constructor <;> dsimp [R] at * <;> linarith⟩
  let Z := pureWZ2PrescribedSlabHull cfg.shading hdelta a b
  let left := pureWZ2PrescribedSlabLeft delta a b
  obtain ⟨hleft, hright, hleftA, hrightB, hslab⟩ :=
    pureWZ2PrescribedSlabHull_height cfg.shading hdelta ha hb
      (hROne.trans (by norm_num)) cfg.cubical
  have hcapZ : ∀ p, (Z.pointMultiplicity p : ENNReal) ≤
      Kakeya.realRpowENN delta (2 - sigma - eta / 8192) * cfg.family.enncard :=
    pureWZ2PrescribedSlabHull_multiplicity cfg.shading hdelta a b cfg.cubical hcap
  have hmassPower : 3 * Kakeya.realRpowENN delta (3 * eta / 32 + 2) ≤
      ENNReal.ofReal (Real.pi / 4) * Kakeya.realRpowENN delta (eta / 16 + 2) := by
    have h := mul_le_mul_of_nonneg_left (massAbsorb delta hdelta hmassCut)
      (by positivity : 0 ≤ Real.pi / 4)
    have hcancel : (Real.pi / 4) * (12 / Real.pi) = 3 := by
      field_simp [Real.pi_ne_zero]
      <;> ring
    rw [← mul_assoc, hcancel] at h
    have h' := ENNReal.ofReal_mono h
    simpa only [Kakeya.realRpowENN, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3),
      ENNReal.ofReal_mul (by positivity : 0 ≤ Real.pi / 4), ENNReal.ofReal_ofNat] using h'
  have hmassZ : Kakeya.realRpowENN delta (3 * eta / 32 + 2) *
      cfg.family.enncard * ENNReal.ofReal R ≤ Z.mass := by
    have hRenn : ENNReal.ofReal R ≤ 3 * ENNReal.ofReal (b - a) := by
      simpa [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)] using ENNReal.ofReal_mono hRle
    calc
      _ ≤ Kakeya.realRpowENN delta (3 * eta / 32 + 2) * cfg.family.enncard *
          (3 * ENNReal.ofReal (b - a)) := by gcongr
      _ = (3 * Kakeya.realRpowENN delta (3 * eta / 32 + 2)) *
          cfg.family.enncard * ENNReal.ofReal (b - a) := by ring
      _ ≤ ENNReal.ofReal (Real.pi / 4) * Kakeya.realRpowENN delta (eta / 16 + 2) *
          cfg.family.enncard * ENNReal.ofReal (b - a) := by gcongr
      _ ≤ paperShadedMassInSlab cfg.shading a b := hmass
      _ ≤ Z.mass := pureWZ2PrescribedSlabHull_mass cfg.shading hdelta a b cfg.cubical
  obtain ⟨refined, hrefined, hrefinedCubical, hretention, hframe⟩ :=
    framePrepare delta hdelta hframeCut cfg Z
      (pureWZ2PrescribedSlabHull_cubical cfg.shading hdelta a b cfg.cubical)
      (pureWZ2PrescribedSlabHull_subshading cfg.shading hdelta a b)
      left (left + R) (by linarith) (by dsimp [R]; linarith)
      hslab (by simpa only [add_sub_cancel_left] using hmassZ) hcapZ
  have hrefinedMass : ENNReal.ofReal (Real.pi / 4) *
      Kakeya.realRpowENN delta (eta / 8 + 2) * cfg.family.enncard *
        ENNReal.ofReal R ≤ refined.mass := by
    have hpower : 2 * ENNReal.ofReal (Real.pi / 4) *
        Kakeya.realRpowENN delta (eta / 8 + 2) ≤
          Kakeya.realRpowENN delta (3 * eta / 32 + 2) := by
      have h := ENNReal.ofReal_mono (retainedAbsorb delta hdelta hretainedCut)
      have hpi : (2 : ENNReal) * ENNReal.ofReal (Real.pi / 4) = ENNReal.ofReal (Real.pi / 2) := by
        rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
        congr 1
        ring
      rw [hpi]
      simpa [Kakeya.realRpowENN, ENNReal.ofReal_mul (by positivity : 0 ≤ Real.pi / 2)] using h
    apply (ENNReal.mul_le_mul_iff_right (by norm_num : (2 : ENNReal) ≠ 0) (by norm_num)).1
    calc
      2 * (ENNReal.ofReal (Real.pi / 4) * Kakeya.realRpowENN delta (eta / 8 + 2) *
          cfg.family.enncard * ENNReal.ofReal R) =
          (2 * ENNReal.ofReal (Real.pi / 4) * Kakeya.realRpowENN delta (eta / 8 + 2)) *
            cfg.family.enncard * ENNReal.ofReal R := by ring
      _ ≤ Kakeya.realRpowENN delta (3 * eta / 32 + 2) *
          cfg.family.enncard * ENNReal.ofReal R := by gcongr
      _ ≤ Z.mass := hmassZ
      _ ≤ 2 * refined.mass := hretention
  have hcoverPower : 9 * Kakeya.realRpowENN delta (-(eta / 16)) ≤
      Kakeya.realRpowENN delta (-(eta / 8)) := by
    have h := ENNReal.ofReal_mono (coverAbsorb delta hdelta hcoverCut)
    simpa [Kakeya.realRpowENN, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 9)] using h
  have hcoverNumber : Kakeya.realRpowENN delta (-(eta / 16)) *
      Kakeya.realRpowENN (b - a) (-2 + sigma) ≤
        Kakeya.realRpowENN delta (-(eta / 8)) * Kakeya.realRpowENN R (-2 + sigma) := by
    calc
      _ ≤ Kakeya.realRpowENN delta (-(eta / 16)) *
          (9 * Kakeya.realRpowENN R (-2 + sigma)) := by
        gcongr
        exact prescribedSlab_cover_power_padding (sub_pos.mpr hab) hR hRle hsigma.le (by linarith)
      _ = (9 * Kakeya.realRpowENN delta (-(eta / 16))) *
          Kakeya.realRpowENN R (-2 + sigma) := by ring
      _ ≤ _ := by gcongr
  have hcoverZ : CanCoverByBalls Z.union R
      (Kakeya.realRpowENN delta (-(eta / 8)) * Kakeya.realRpowENN R (-2 + sigma)) := by
    obtain ⟨centers, hcard, hballs⟩ :=
      pureWZ2PrescribedSlabHull_cover cfg.shading hdelta a b cfg.cubical hcover
    exact ⟨centers, hcard.trans hcoverNumber, hballs⟩
  have hrefinedCap : ∀ p, (refined.pointMultiplicity p : ENNReal) ≤
      Kakeya.realRpowENN delta (2 - sigma - eta / 8192) * cfg.family.enncard := by
    intro p
    have hnat : refined.pointMultiplicity p ≤ Z.pointMultiplicity p := by
      apply Finset.card_le_card
      intro i hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrefined i (Finset.mem_filter.mp hi).2⟩
    exact (show (refined.pointMultiplicity p : ENNReal) ≤ (Z.pointMultiplicity p : ENNReal)
      by exact_mod_cast hnat).trans (hcapZ p)
  have hexponent : 0 ≤ 2 - sigma - eta / 8 := by linarith
  have hdeltaDiv : delta ≤ delta / R := by
    apply (le_div_iff₀ hR).2
    nlinarith
  have hweakPower : Kakeya.realRpowENN delta (2 - sigma - eta / 8192) ≤
      Kakeya.realRpowENN (delta / R) (2 - sigma - eta / 8) := by
    apply ENNReal.ofReal_mono
    exact (Real.rpow_le_rpow_of_exponent_ge hdelta hdeltaOne (by linarith)).trans
      (Real.rpow_le_rpow hdelta.le hdeltaDiv hexponent)
  have hstrongPower : Kakeya.realRpowENN delta (2 - sigma - eta / 8192) ≤
      Kakeya.realRpowENN delta (2 - sigma - eta / 4096) *
        Kakeya.realRpowENN R (-(eta / 4096)) := by
    have hfirst : Kakeya.realRpowENN delta (2 - sigma - eta / 8192) ≤
        Kakeya.realRpowENN delta (2 - sigma - eta / 4096) :=
      ENNReal.ofReal_mono (Real.rpow_le_rpow_of_exponent_ge hdelta hdeltaOne (by linarith))
    have hone : (1 : ENNReal) ≤ Kakeya.realRpowENN R (-(eta / 4096)) := by
      have h : Real.rpow R 0 ≤ Real.rpow R (-(eta / 4096)) :=
        Real.rpow_le_rpow_of_exponent_ge hR hROne (by linarith)
      have h' := ENNReal.ofReal_mono h
      simpa [Kakeya.realRpowENN] using h'
    exact hfirst.trans (le_mul_of_one_le_right' hone)
  let slabData : PureWZ2Section6ScaleData cfg.shading sigma (eta / 8) scale :=
    { slabLeft := left
      slabRight := left + R
      slabLeft_mem := hleft
      slab_ordered := by linarith
      slabRight_mem := hright
      slab_width := by change left + R - left = R; ring
      slabShading := refined
      slab_subshading := fun i => (hrefined i).trans
        (pureWZ2PrescribedSlabHull_subshading cfg.shading hdelta a b i)
      slab_cubical := hrefinedCubical
      slab_in_slab := fun i => (hrefined i).trans (hslab i)
      slab_mass := hrefinedMass
      slab_cover := CanCoverByBalls.mono hrefined.union_subset hcoverZ
      slab_pointMultiplicity_upper := fun p => (hrefinedCap p).trans (by gcongr) }
  let data : PureWZ2Lemma66PreparedIntervalOn sigma eta delta :=
    { cfg := cfg
      rho := scale
      globalSlope := f
      globalSlope_eq_on := hf
      globalSlope_normalized := hnormalized
      scaleData := slabData
      frameNormalCompatibility := hframe
      pointMultiplicity_upper := fun p => (hrefinedCap p).trans (by gcongr) }
  intro z hz
  have hz' : z ∈ Set.Icc slabData.slabLeft slabData.slabRight :=
    ⟨hleftA.trans hz.1, hz.2.trans hrightB⟩
  have hderiv := prepared delta hdelta hprepared data
    (hlower.trans (by change b - a ≤ R; dsimp [R]; linarith)) hRpower z hz'
  have hRderiv : R ≤ |deriv f z| := by simpa [data, slabData] using hderiv
  exact (show b - a ≤ R by dsimp [R]; linarith).trans hRderiv

end Kakeya.Assouad
end
