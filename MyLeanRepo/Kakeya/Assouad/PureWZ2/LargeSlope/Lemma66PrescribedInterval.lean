import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.Lemma66PreparedInterval
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.PrescribedSlabHull
import MyLeanRepo.Kakeya.Assouad.ConstantAbsorption

/-!
# Lemma 6.6 for a prescribed interval before whole-cell preparation

The input interval is arbitrary. Its raw slab mass and cover are converted
to the whole-cell data required by the prepared derivative lemma, with a
cutoff fixed before the interval is supplied. One multiplicity bound inside
the raw slab implies both prepared multiplicity bounds after taking the hull.

The remaining hypotheses are stated explicitly: frame compatibility and a
fine multiplicity cap. The mass hypothesis is normalized by delta^2*#T.
This module does not claim to derive those facts from the printed absolute
mass hypothesis alone.
-/

noncomputable section
open MeasureTheory Set
namespace Kakeya.Assouad

theorem prescribedSlab_cover_power_padding {rho R sigma : ℝ}
    (hrho : 0 < rho) (hR : 0 < R) (hRle : R ≤ 3 * rho)
    (hsigma : 0 ≤ sigma) (hsigmaTwo : sigma ≤ 2) :
    Kakeya.realRpowENN rho (-2 + sigma) ≤
      9 * Kakeya.realRpowENN R (-2 + sigma) := by
  have hthree : (1 / 9 : ℝ) ≤ Real.rpow 3 (-2 + sigma) := by
    have h : Real.rpow 3 (-2) ≤ Real.rpow 3 (-2 + sigma) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    norm_num at h
    exact h
  have hmono : Real.rpow (3 * rho) (-2 + sigma) ≤ Real.rpow R (-2 + sigma) :=
    Real.rpow_le_rpow_of_nonpos hR hRle (by linarith)
  have hproduct : Real.rpow (3 * rho) (-2 + sigma) =
      Real.rpow 3 (-2 + sigma) * Real.rpow rho (-2 + sigma) :=
    Real.mul_rpow (by norm_num) hrho.le
  have hsmall : (1 / 9 : ℝ) * Real.rpow rho (-2 + sigma) ≤
      Real.rpow R (-2 + sigma) := by
    calc
      _ ≤ Real.rpow 3 (-2 + sigma) * Real.rpow rho (-2 + sigma) :=
        mul_le_mul_of_nonneg_right hthree (Real.rpow_nonneg hrho.le _)
      _ = Real.rpow (3 * rho) (-2 + sigma) := hproduct.symm
      _ ≤ _ := hmono
  have hreal : Real.rpow rho (-2 + sigma) ≤ 9 * Real.rpow R (-2 + sigma) := by
    linarith
  have h := ENNReal.ofReal_mono hreal
  simpa only [Kakeya.realRpowENN, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 9),
    ENNReal.ofReal_ofNat] using h

/-- Arbitrary prescribed intervals need no separate whole-cell input. The
remaining frame and multiplicity preparation is visible in the statement. -/
theorem pure_wz2_lemma66_prescribed_interval
    (sigma epsilon eta : ℝ)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hepsilon : 0 < epsilon) (hepsilonHalf : epsilon ≤ 1 / 2)
    (heta : 0 < eta) (hbudget : 2000 * eta ≤ epsilon * sigma ^ 2) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
        ∀ cfg : PureWZ2C2GrainConfiguration sigma (eta / 8) delta,
          PureWZ2FrameNormalCompatibility cfg →
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
  obtain ⟨preparedScale, hpreparedScale, hpreparedOne, prepared⟩ :=
    pure_wz2_lemma66_prepared_interval sigma (epsilon / 2) eta hsigma hsigmaOne
      (by positivity) (by linarith) heta (by nlinarith)
  obtain ⟨massScale, hmassScale, _, massAbsorb⟩ :=
    exists_delta_mul_rpow_le_rpow 3 (by norm_num)
      (show eta / 16 + 2 < eta / 8 + 2 by linarith)
  obtain ⟨coverScale, hcoverScale, _, coverAbsorb⟩ :=
    exists_delta_mul_rpow_le_rpow 9 (by norm_num)
      (show -(eta / 8) < -(eta / 16) by linarith)
  obtain ⟨widthScale, hwidthScale, _, widthAbsorb⟩ :=
    exists_delta_mul_rpow_le_rpow 3 (by norm_num)
      (show epsilon / 2 < epsilon by linarith)
  let delta₀ := min preparedScale (min massScale (min coverScale widthScale))
  refine ⟨delta₀, by dsimp [delta₀]; positivity,
    (min_le_left _ _).trans hpreparedOne, ?_⟩
  intro delta hdelta hcut cfg hframe f hf hnormalized a b ha hab hb hlower hupper hmass hcover hcap
  have hprepared : delta ≤ preparedScale := hcut.trans (by simp [delta₀])
  have hmassCut : delta ≤ massScale := hcut.trans (by simp [delta₀])
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
  have hmassPower : 3 * Kakeya.realRpowENN delta (eta / 8 + 2) ≤
      Kakeya.realRpowENN delta (eta / 16 + 2) := by
    have h := ENNReal.ofReal_mono (massAbsorb delta hdelta hmassCut)
    simpa [Kakeya.realRpowENN, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)] using h
  have hmassZ : ENNReal.ofReal (Real.pi / 4) * Kakeya.realRpowENN delta (eta / 8 + 2) *
      cfg.family.enncard * ENNReal.ofReal R ≤ Z.mass := by
    have hRenn : ENNReal.ofReal R ≤ 3 * ENNReal.ofReal (b - a) := by
      simpa [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)] using ENNReal.ofReal_mono hRle
    calc
      _ ≤ ENNReal.ofReal (Real.pi / 4) * Kakeya.realRpowENN delta (eta / 8 + 2) *
          cfg.family.enncard * (3 * ENNReal.ofReal (b - a)) := by gcongr
      _ = ENNReal.ofReal (Real.pi / 4) * (3 * Kakeya.realRpowENN delta (eta / 8 + 2)) *
          cfg.family.enncard * ENNReal.ofReal (b - a) := by ring
      _ ≤ ENNReal.ofReal (Real.pi / 4) * Kakeya.realRpowENN delta (eta / 16 + 2) *
          cfg.family.enncard * ENNReal.ofReal (b - a) := by gcongr
      _ ≤ paperShadedMassInSlab cfg.shading a b := hmass
      _ ≤ Z.mass := pureWZ2PrescribedSlabHull_mass cfg.shading hdelta a b cfg.cubical
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
  have hetaSmall : eta ≤ 1 := by
    have hsigmaSq : sigma ^ 2 ≤ 1 := by nlinarith
    have hprod : epsilon * sigma ^ 2 ≤ epsilon := by nlinarith
    linarith
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
      have hzero : Real.rpow R 0 = 1 := Real.rpow_zero R
      rw [hzero] at h
      have h' := ENNReal.ofReal_mono h
      rw [ENNReal.ofReal_one] at h'
      exact h'
    exact hfirst.trans (le_mul_of_one_le_right' hone)
  let slabData : PureWZ2Section6ScaleData cfg.shading sigma (eta / 8) scale :=
    { slabLeft := left
      slabRight := left + R
      slabLeft_mem := hleft
      slab_ordered := by linarith
      slabRight_mem := hright
      slab_width := by change left + R - left = R; ring
      slabShading := Z
      slab_subshading := pureWZ2PrescribedSlabHull_subshading cfg.shading hdelta a b
      slab_cubical := pureWZ2PrescribedSlabHull_cubical cfg.shading hdelta a b cfg.cubical
      slab_in_slab := hslab
      slab_mass := hmassZ
      slab_cover := hcoverZ
      slab_pointMultiplicity_upper := fun p => (hcapZ p).trans (by gcongr) }
  let data : PureWZ2Lemma66PreparedInterval sigma eta delta :=
    { cfg := cfg
      rho := scale
      globalSlope := f
      globalSlope_eq_on := hf
      globalSlope_normalized := hnormalized
      scaleData := slabData
      frameNormalCompatibility := hframe
      pointMultiplicity_upper := fun p => (hcapZ p).trans (by gcongr) }
  intro z hz
  have hz' : z ∈ Set.Icc slabData.slabLeft slabData.slabRight :=
    ⟨hleftA.trans hz.1, hz.2.trans hrightB⟩
  have hderiv := prepared delta hdelta hprepared data
    (hlower.trans (by change b - a ≤ R; dsimp [R]; linarith)) hRpower z hz'
  have hRderiv : R ≤ |deriv f z| := by simpa [data, slabData] using hderiv
  exact (show b - a ≤ R by dsimp [R]; linarith).trans hRderiv

end Kakeya.Assouad
end
