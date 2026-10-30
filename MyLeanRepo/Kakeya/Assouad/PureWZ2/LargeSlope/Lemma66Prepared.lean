import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.Lemma66PreparedInterval
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.Section6Lemma31Contradiction
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.FaithfulStep4Numerics
import MyLeanRepo.Kakeya.Assouad.WZ1.Corollary26DeltaBudget

/-!
# An independent, prepared-input form of WZ2 Lemma 6.6

This theorem quantifies over every prepared power-scale slab.  Its input
contains C2 grains, the selected shading and its mass/covering data, frame
compatibility, and a multiplicity upper bound.  It does not contain a
derivative lower bound, a convex-overload theorem, or a critical package.

The interval-length restriction is removed in `Lemma66PreparedInterval`.
The generic paper lemma still needs preparation from its two printed hypotheses.  That additional theorem is not
asserted here.  The power-scale construction used by Proposition 6.5 supplies
exactly the prepared data below.
-/

noncomputable section
namespace Kakeya.Assouad

/-- The analytic and geometric input to the prepared Lemma 6.6 proof. -/
structure PureWZ2Lemma66PreparedSlab
    (sigma epsilon eta delta : ℝ) where
  cfg : PureWZ2C2GrainConfiguration sigma (eta / 8) delta
  rho : WZ2PaperRequestedScale delta
  rho_eq_power : rho.1 = Real.rpow delta epsilon
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

/-- Remove the proof-valued overload field at the preparation boundary. -/
def PureWZ2Lemma31ScaleAssembly.toLemma66PreparedSlab
    {sigma epsilon delta : ℝ}
    (data : PureWZ2Lemma31ScaleAssembly sigma epsilon delta) :
    PureWZ2Lemma66PreparedSlab sigma epsilon data.eta delta := by
  rcases data with ⟨eta, heta, hbudget, targetLoss, htarget,
    stickyLoss, hsticky, sourceLoss, hsource, hsourceSticky,
    cfg, hbounded, rho, hrho, slope, hslope, hnormalized,
    scaleData, frame, _overload, multiplicity⟩
  subst targetLoss
  subst stickyLoss
  exact ⟨cfg, rho, hrho, slope, hslope, hnormalized, scaleData, frame, multiplicity⟩

/-- Removing the overload field changes neither the interval nor its slope. -/
theorem PureWZ2Lemma31ScaleAssembly.toLemma66PreparedSlab_coordinates
    {sigma epsilon delta : ℝ}
    (data : PureWZ2Lemma31ScaleAssembly sigma epsilon delta) :
    data.toLemma66PreparedSlab.scaleData.slabLeft = data.scaleData.slabLeft ∧
      data.toLemma66PreparedSlab.scaleData.slabRight = data.scaleData.slabRight ∧
      data.toLemma66PreparedSlab.globalSlope = data.globalSlope := by
  rcases data with ⟨eta, heta, hbudget, targetLoss, htarget,
    stickyLoss, hsticky, sourceLoss, hsource, hsourceSticky,
    cfg, hbounded, rho, hrho, slope, hslope, hnormalized,
    scaleData, frame, overload, multiplicity⟩
  subst targetLoss
  subst stickyLoss
  exact ⟨rfl, rfl, rfl⟩

/-- Independent closed prepared-slab lemma.  All scalar thresholds precede
the runtime scale, family, slope, and slab.  In particular convex overload is
proved here, rather than requested as an external proof input. -/
theorem pure_wz2_lemma66_prepared
    (sigma epsilon eta : ℝ)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hepsilon : 0 < epsilon) (hepsilonHalf : epsilon ≤ 1 / 2)
    (heta : 0 < eta) (hbudget : 1000 * eta ≤ epsilon * sigma ^ 2) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
        ∀ data : PureWZ2Lemma66PreparedSlab sigma epsilon eta delta,
          ∀ z ∈ Set.Icc data.scaleData.slabLeft data.scaleData.slabRight,
            data.scaleData.slabRight - data.scaleData.slabLeft ≤
              |deriv data.globalSlope z| := by
  obtain ⟨delta₀, hd, hd1, hinterval⟩ :=
    pure_wz2_lemma66_prepared_interval sigma epsilon eta hsigma hsigmaOne
      hepsilon hepsilonHalf heta hbudget
  refine ⟨delta₀, hd, hd1, ?_⟩
  intro delta hdelta hsmall data
  let interval : PureWZ2Lemma66PreparedInterval sigma eta delta := {
    cfg := data.cfg
    rho := data.rho
    globalSlope := data.globalSlope
    globalSlope_eq_on := data.globalSlope_eq_on
    globalSlope_normalized := data.globalSlope_normalized
    scaleData := data.scaleData
    frameNormalCompatibility := data.frameNormalCompatibility
    pointMultiplicity_upper := data.pointMultiplicity_upper }
  have hlower : Real.rpow delta (1 / 2) ≤ interval.rho.1 := by
    change Real.rpow delta (1 / 2) ≤ data.rho.1
    rw [data.rho_eq_power]
    exact Real.rpow_le_rpow_of_exponent_ge hdelta (hsmall.trans hd1) hepsilonHalf
  exact hinterval delta hdelta hsmall interval hlower data.rho_eq_power.le

end Kakeya.Assouad
end
