import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.Section6Lemma31Contradiction
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.FaithfulStep4Numerics
import MyLeanRepo.Kakeya.Assouad.WZ1.Corollary26DeltaBudget

/-!
# Uniform prepared Lemma 6.6 on the full interval-length range

The interval length may vary anywhere between sqrt(delta) and delta^epsilon.
The cutoff is uniform over that range.  Frame compatibility and the two
multiplicity caps remain explicit geometric preparation hypotheses; this
module does not derive them from the paper's mass and covering assumptions.
-/

noncomputable section
namespace Kakeya.Assouad

/-- Prepared geometric input without a prescribed power-scale length. -/
structure PureWZ2Lemma66PreparedInterval
    (sigma eta delta : ℝ) where
  cfg : PureWZ2C2GrainConfiguration sigma (eta / 8) delta
  rho : WZ2PaperRequestedScale delta
  globalSlope : SlopeFunction
  globalSlope_eq_on : ∀ z ∈ Set.Icc (-1 : ℝ) 1,
    globalSlope z = cfg.globalGrains.slope z
  globalSlope_normalized : globalSlope.IsNormalized
  scaleData : PureWZ2Section6ScaleData cfg.shading sigma (eta / 8) rho
  frameNormalCompatibility : PureWZ2FrameNormalCompatibility cfg
  pointMultiplicity_upper : ∀ point,
    (scaleData.slabShading.pointMultiplicity point : ENNReal) ≤
      (Kakeya.realRpowENN delta (2 - sigma - eta / 4096) *
        Kakeya.realRpowENN rho.1 (-(eta / 4096))) * cfg.family.enncard

/-- Prepared input requiring the normal certificate only on its slab. -/
structure PureWZ2Lemma66PreparedIntervalOn
    (sigma eta delta : ℝ) where
  cfg : PureWZ2C2GrainConfiguration sigma (eta / 8) delta
  rho : WZ2PaperRequestedScale delta
  globalSlope : SlopeFunction
  globalSlope_eq_on : ∀ z ∈ Set.Icc (-1 : ℝ) 1,
    globalSlope z = cfg.globalGrains.slope z
  globalSlope_normalized : globalSlope.IsNormalized
  scaleData : PureWZ2Section6ScaleData cfg.shading sigma (eta / 8) rho
  frameNormalCompatibility : PureWZ2FrameNormalCompatibilityOn cfg scaleData.slabShading.union
  pointMultiplicity_upper : ∀ point,
    (scaleData.slabShading.pointMultiplicity point : ENNReal) ≤
      (Kakeya.realRpowENN delta (2 - sigma - eta / 4096) *
        Kakeya.realRpowENN rho.1 (-(eta / 4096))) * cfg.family.enncard

/-- The prepared derivative bound is uniform over the paper's entire
interval-length range.  The logarithmic exponent is introduced only inside
the proof, after the uniform cutoff has been fixed. -/
theorem pure_wz2_lemma66_prepared_interval_on
    (sigma epsilon eta : ℝ)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hepsilon : 0 < epsilon) (hepsilonHalf : epsilon ≤ 1 / 2)
    (heta : 0 < eta) (hbudget : 1000 * eta ≤ epsilon * sigma ^ 2) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
        ∀ data : PureWZ2Lemma66PreparedIntervalOn sigma eta delta,
          Real.rpow delta (1 / 2) ≤ data.rho.1 →
          data.rho.1 ≤ Real.rpow delta epsilon →
          ∀ z ∈ Set.Icc data.scaleData.slabLeft data.scaleData.slabRight,
            data.scaleData.slabRight - data.scaleData.slabLeft ≤
              |deriv data.globalSlope z| := by
  have hsigmaSq : sigma ^ 2 < 1 := by
    nlinarith [mul_pos hsigma (sub_pos.mpr hsigmaOne)]
  have hetaEpsilon : eta ≤ epsilon := by
    nlinarith [mul_nonneg hepsilon.le (sub_pos.mpr hsigmaSq).le]
  rcases large_slope_faithful_convex_overload epsilon sigma eta (eta / 8)
      hepsilon hepsilonHalf hsigma hsigmaOne heta hetaEpsilon
      (by linarith) hbudget with
    ⟨overloadScale, hoverloadScale, hoverloadOne, overload⟩
  have hcommonExponent :
      0 < 4 * (eta / 2) - eta / 8 - eta / 8 -
        (1 + (1 / 2 : ℝ)) * (eta / 4096) := by
    nlinarith [mul_nonneg heta.le (sub_nonneg.mpr hepsilonHalf)]
  rcases exists_delta_rpow_le_single
      (4 * (eta / 2) - eta / 8 - eta / 8 - (1 + (1 / 2 : ℝ)) * (eta / 4096))
      (1 / 400000) hcommonExponent (by norm_num) (by norm_num) with
    ⟨commonScale, hcommonScale, _, common⟩
  rcases exists_delta_rpow_le_single
      (12 * eta - 4 * (eta / 2) - eta / 8) (1 / 100000)
      (by linarith) (by norm_num) (by norm_num) with
    ⟨prismScale, hprismScale, _, prism⟩
  rcases pureWZ2_faithfulStep4_delta_exists
      (eta := eta) (loss := eta / 8) (by linarith) with
    ⟨wholeScale, hwholeScale, _, whole⟩
  rcases exists_delta_rpow_le_single (1 / 2) (1 / 256)
      (by norm_num) (by norm_num) (by norm_num) with
    ⟨geometryScale, hgeometryScale, _, geometry⟩
  rcases exists_delta_rpow_le_single epsilon (1 / 100)
      hepsilon (by norm_num) (by norm_num) with
    ⟨rhoScale, hrhoScale, _, smallRho⟩
  let delta₀ := min (1 / 100 : ℝ) <| min overloadScale <|
    min commonScale <| min prismScale <| min wholeScale <|
      min geometryScale rhoScale
  refine ⟨delta₀, by dsimp only [delta₀]; positivity,
    (min_le_left _ _).trans (by norm_num), ?_⟩
  intro delta hdelta hdeltaBound data hlower hupper
  have hsmall : delta ≤ 1 / 100 :=
    hdeltaBound.trans (by simp [delta₀])
  have hone : delta ≤ 1 := hsmall.trans (by norm_num)
  have ho : delta ≤ overloadScale := hdeltaBound.trans (by simp [delta₀])
  have hc : delta ≤ commonScale := hdeltaBound.trans (by simp [delta₀])
  have hp : delta ≤ prismScale := hdeltaBound.trans (by simp [delta₀])
  have hw : delta ≤ wholeScale := hdeltaBound.trans (by simp [delta₀])
  have hg : delta ≤ geometryScale := hdeltaBound.trans (by simp [delta₀])
  have hr : delta ≤ rhoScale := hdeltaBound.trans (by simp [delta₀])
  have hrho : data.rho.1 ≤ 1 / 100 :=
    hupper.trans (smallRho delta hdelta hr)
  have hrhoPos : 0 < data.rho.1 := hdelta.trans_le data.rho.2.1
  have hlog : Real.log delta < 0 := Real.log_neg hdelta (by linarith)
  let power : ℝ := Real.log data.rho.1 / Real.log delta
  have hpower : Real.rpow delta power = data.rho.1 := by
    change delta ^ power = data.rho.1
    rw [Real.rpow_def_of_pos hdelta]
    dsimp only [power]
    rw [show Real.log delta * (Real.log data.rho.1 / Real.log delta) =
      Real.log data.rho.1 by field_simp [hlog.ne]]
    exact Real.exp_log hrhoPos
  have hpowerLower : epsilon ≤ power := by
    apply (Real.rpow_le_rpow_left_iff_of_base_lt_one hdelta (by linarith)).mp
    change Real.rpow delta power ≤ Real.rpow delta epsilon
    rw [hpower]
    exact hupper
  have hpowerHalf : power ≤ 1 / 2 := by
    apply (Real.rpow_le_rpow_left_iff_of_base_lt_one hdelta (by linarith)).mp
    change Real.rpow delta (1 / 2) ≤ Real.rpow delta power
    rw [hpower]
    exact hlower
  have hgeometry : 256 * delta ≤ data.rho.1 := by
    have hsplit : delta = Real.rpow delta (1 / 2) * Real.rpow delta (1 / 2) := by
      change delta = delta ^ (1 / 2 : ℝ) * delta ^ (1 / 2 : ℝ)
      rw [← Real.rpow_add hdelta]
      norm_num
    calc
      256 * delta = 256 * (Real.rpow delta (1 / 2) * Real.rpow delta (1 / 2)) := by rw [← hsplit]
      _ ≤ 256 * (Real.rpow delta (1 / 2) * (1 / 256)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (geometry delta hdelta hg)
            (Real.rpow_nonneg hdelta.le _)) (by norm_num)
      _ = Real.rpow delta (1 / 2) := by ring
      _ ≤ data.rho.1 := hlower
  have hcommon : Kakeya.realRpowENN delta
      (4 * (eta / 2) - eta / 8 - eta / 8 -
        (1 + power) * (eta / 4096)) ≤ ENNReal.ofReal (1 / 400000 : ℝ) := by
    apply LE.le.trans _ (ENNReal.ofReal_mono (common delta hdelta hc))
    apply ENNReal.ofReal_le_ofReal
    apply Real.rpow_le_rpow_of_exponent_ge hdelta hone
    nlinarith [mul_nonneg (sub_nonneg.mpr hpowerHalf) (show 0 ≤ eta / 4096 by positivity)]
  have hlocal : (36 : ENNReal) *
      (20 * Kakeya.realRpowENN delta (-(eta / 8))) ≤
        Kakeya.realRpowENN delta (-(12 * eta)) :=
    (mul_le_mul_right' (by norm_num : (36 : ENNReal) ≤ 4356)
      (20 * Kakeya.realRpowENN delta (-(eta / 8)))).trans
        (pureWZ2_faithful_whole_ad_constant hdelta hone (by positivity)
          (whole delta hdelta hw))
  let assembled : PureWZ2Lemma31SlabAssembly sigma power delta :=
    { eta := eta
      eta_pos := heta
      eta_budget := by nlinarith [sq_nonneg sigma, mul_nonneg (sub_nonneg.mpr hpowerLower) (sq_nonneg sigma)]
      targetLoss := eta / 8
      targetLoss_eq := rfl
      stickyLoss := eta / 4096
      stickyLoss_eq := rfl
      sourceLoss := eta / 4096
      sourceLoss_pos := by positivity
      sourceLoss_le_stickyLoss := le_rfl
      cfg := data.cfg
      cfg_bounded_base := data.cfg.bounded_base
      rho := data.rho
      rho_eq_power := hpower.symm
      globalSlope := data.globalSlope
      globalSlope_eq_on := data.globalSlope_eq_on
      globalSlope_normalized := data.globalSlope_normalized
      scaleData := data.scaleData
      frameNormalCompatibility := data.frameNormalCompatibility
      faithful_overload := fun a b hab step4 =>
        overload delta hdelta ho data.cfg a b
          (hab.trans (by simpa only [hpower] using hupper)) step4
      pointMultiplicity_upper := data.pointMultiplicity_upper }
  exact assembled.derivative_lower (hepsilon.trans_le hpowerLower) hpowerHalf hsigma hsigmaOne
    (by linarith) hsmall hgeometry (hrho.trans (by norm_num))
    (by dsimp [assembled]; nlinarith [hrho, hrhoPos])
    (by dsimp [assembled]; nlinarith [hrho, hrhoPos])
    hcommon (prism delta hdelta hp) hlocal
    assembled.faithful_overload

/-- Compatibility entry with the original global frame hypothesis. -/
theorem pure_wz2_lemma66_prepared_interval
    (sigma epsilon eta : ℝ)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hepsilon : 0 < epsilon) (hepsilonHalf : epsilon ≤ 1 / 2)
    (heta : 0 < eta) (hbudget : 1000 * eta ≤ epsilon * sigma ^ 2) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
        ∀ data : PureWZ2Lemma66PreparedInterval sigma eta delta,
          Real.rpow delta (1 / 2) ≤ data.rho.1 →
          data.rho.1 ≤ Real.rpow delta epsilon →
          ∀ z ∈ Set.Icc data.scaleData.slabLeft data.scaleData.slabRight,
            data.scaleData.slabRight - data.scaleData.slabLeft ≤
              |deriv data.globalSlope z| := by
  obtain ⟨delta₀, hdelta₀, hdelta₀One, prepared⟩ :=
    pure_wz2_lemma66_prepared_interval_on sigma epsilon eta hsigma hsigmaOne
      hepsilon hepsilonHalf heta hbudget
  refine ⟨delta₀, hdelta₀, hdelta₀One, ?_⟩
  intro delta hdelta hcut data hlower hupper
  let localData : PureWZ2Lemma66PreparedIntervalOn sigma eta delta :=
    { cfg := data.cfg
      rho := data.rho
      globalSlope := data.globalSlope
      globalSlope_eq_on := data.globalSlope_eq_on
      globalSlope_normalized := data.globalSlope_normalized
      scaleData := data.scaleData
      frameNormalCompatibility := data.frameNormalCompatibility.on _
      pointMultiplicity_upper := data.pointMultiplicity_upper }
  exact prepared delta hdelta hcut localData hlower hupper

end Kakeya.Assouad
end
