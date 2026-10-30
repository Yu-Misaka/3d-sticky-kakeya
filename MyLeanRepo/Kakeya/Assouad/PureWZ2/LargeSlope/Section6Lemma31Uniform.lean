import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.Lemma66Prepared
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.FaithfulStep4Numerics
import MyLeanRepo.Kakeya.Assouad.WZ1.Corollary26DeltaBudget

/-!
# Uniform WZ2 Lemma 31 assembly

The final Lemma-31 slab is selected at the paper scale `rho = delta^epsilon`.
The paper-facing C2 and universal Proposition 6.2 providers are independent;
Node 6 constructs the frame-normal compatibility needed by the power-scale
contradiction.
-/

noncomputable section
namespace Kakeya.Assouad

open MeasureTheory Set

/-- The numerical loss in the centered-conflict estimate after coupling the
anisotropic slope scale to the final similarity. -/
def pureWZ2CoupledConflictConstant : ℝ := 480000000000000000

/-- A fixed lower bound for the final similarity.  The first term pays for
the pullback of target balls; the second pays for the completed-normal
Lipschitz constant with the canonical final target constant. -/
def pureWZ2CoupledScaleRequirement : ℝ :=
  max 15000 (1536 * (lipschitzExtensionConstant Point3 : ℝ))

theorem pureWZ2CoupledScaleRequirement_pos :
    0 < pureWZ2CoupledScaleRequirement := by
  unfold pureWZ2CoupledScaleRequirement
  exact lt_of_lt_of_le (by norm_num) (le_max_left _ _)

/-- One power-scale Lemma-31 configuration together with its derivative lower
bound on the selected slab. -/
structure PureWZ2Lemma31DerivativeAssembly
    (sigma epsilon delta : ℝ) where
  data : PureWZ2Lemma31ScaleAssembly sigma epsilon delta
  sigma_pos : 0 < sigma
  epsilon_pos : 0 < epsilon
  eta : ℝ
  eta_eq : eta = data.eta
  eta_pos : 0 < eta
  eta_budget : 1000 * eta ≤ epsilon * sigma ^ 2
  delta_small : delta ≤ 1 / 100
  rho_tiny : data.rho.1 ≤ 1 / 240000000000000000
  rho_coupled_tiny : data.rho.1 ≤
    1 / (pureWZ2CoupledConflictConstant *
      pureWZ2CoupledScaleRequirement)
  delta_le_rho_sq : delta ≤ data.rho.1 ^ 2
  delta_le_rho_eight : delta ≤ data.rho.1 ^ 8
  common_y_small : Kakeya.realRpowENN delta
      (4 * (eta / 2) - data.targetLoss - data.targetLoss -
        (1 + epsilon) * data.stickyLoss) ≤
    ENNReal.ofReal (1 / 400000 : ℝ)
  derivative_lower :
    ∀ z ∈ Set.Icc data.scaleData.slabLeft data.scaleData.slabRight,
      data.scaleData.slabRight - data.scaleData.slabLeft ≤
        |deriv data.globalSlope z|

/-- The uniform contradiction layer only needs a producer of the minimal
Lemma-31 scale record.  Keeping that producer abstract lets the historical
universal interface and the self-contained fixed-scale implementation share
the same numerical and geometric proof. -/
theorem pureWZ2_lemma31_derivative_assembly_with_eta_of_scale_producer
    (sigma epsilon eta : ℝ)
    (scaleProducer : ∀ deltaBound : ℝ, 0 < deltaBound →
      ∃ delta : ℝ, 0 < delta ∧ delta ≤ deltaBound ∧
        ∃ data : PureWZ2Lemma31ScaleAssembly sigma epsilon delta,
          data.eta = eta)
    (critical : PureWZ2CriticalPackage sigma)
    (deltaBound : ℝ)
    (hepsilon : 0 < epsilon) (hepsilonEighth : epsilon ≤ 1 / 8)
    (heta : 0 < eta) (hetaBudget : 1000 * eta ≤ epsilon * sigma ^ 2)
    (hdeltaBound : 0 < deltaBound) :
    ∃ delta : ℝ, 0 < delta ∧ delta ≤ deltaBound ∧
      ∃ data : PureWZ2Lemma31DerivativeAssembly sigma epsilon delta,
        data.eta = eta := by
  have hepsilonHalf : epsilon ≤ 1 / 2 :=
    hepsilonEighth.trans (by norm_num)
  let targetLoss : ℝ := eta / 8
  let stickyLoss : ℝ := eta / 4096
  rcases pure_wz2_lemma66_prepared sigma epsilon eta
      critical.sigma_pos critical.sigma_lt_one hepsilon hepsilonHalf
      heta hetaBudget with ⟨deltaLemma66, hdeltaLemma66, _, lemma66⟩
  have hcommonExponent' :
      0 < 4 * (eta / 2) - targetLoss - targetLoss -
        (1 + epsilon) * stickyLoss := by
    dsimp only [targetLoss, stickyLoss]
    nlinarith [mul_pos heta (sub_pos.mpr (by linarith : epsilon < 7))]
  rcases exists_delta_rpow_le_single
      (4 * (eta / 2) - targetLoss - targetLoss -
        (1 + epsilon) * stickyLoss)
      (1 / 400000) hcommonExponent'
      (by norm_num) (by norm_num) with
    ⟨deltaCommon, hdeltaCommon, _hdeltaCommonOne, hcommon⟩
  rcases exists_delta_rpow_le_single epsilon
      (1 / 240000000000000000) hepsilon
      (by norm_num) (by norm_num) with
    ⟨deltaRho, hdeltaRho, _hdeltaRhoOne, hrhoSmall⟩
  have hcoupledThreshold : 0 <
      1 / (pureWZ2CoupledConflictConstant *
        pureWZ2CoupledScaleRequirement) := by
    exact one_div_pos.mpr <| mul_pos (by
      unfold pureWZ2CoupledConflictConstant
      norm_num) pureWZ2CoupledScaleRequirement_pos
  rcases exists_delta_rpow_le_single epsilon
      (1 / (pureWZ2CoupledConflictConstant *
        pureWZ2CoupledScaleRequirement)) hepsilon
      hcoupledThreshold (by
        have hrequirement : 1 ≤ pureWZ2CoupledScaleRequirement := by
          unfold pureWZ2CoupledScaleRequirement
          exact (by norm_num : (1 : ℝ) ≤ 15000).trans (le_max_left _ _)
        have hdenomPos : 0 < pureWZ2CoupledConflictConstant *
            pureWZ2CoupledScaleRequirement :=
          mul_pos (by unfold pureWZ2CoupledConflictConstant; norm_num)
            pureWZ2CoupledScaleRequirement_pos
        apply (div_lt_one hdenomPos).2
        unfold pureWZ2CoupledConflictConstant
        nlinarith) with
    ⟨deltaCoupled, hdeltaCoupled, _hdeltaCoupledOne, hcoupledSmall⟩
  let smallScale := deltaLemma66 ⊓ deltaCommon ⊓ deltaRho ⊓ deltaCoupled
  let requestedBound := min deltaBound (min smallScale (1 / 100))
  have hrequestedBound : 0 < requestedBound := by
    dsimp only [requestedBound, smallScale]
    positivity
  rcases scaleProducer requestedBound hrequestedBound with
    ⟨delta, hdelta, hdeltaRequested, data, hdataEta⟩
  have hdeltaBound' : delta ≤ deltaBound :=
    hdeltaRequested.trans (by simp [requestedBound])
  have hdeltaSmall : delta ≤ 1 / 100 :=
    hdeltaRequested.trans (by simp [requestedBound])
  have hdeltaLemma66Le : delta ≤ deltaLemma66 :=
    hdeltaRequested.trans (by simp [requestedBound, smallScale])
  have hdeltaCommonLe : delta ≤ deltaCommon :=
    hdeltaRequested.trans (by simp [requestedBound, smallScale])
  have hdeltaRhoLe : delta ≤ deltaRho :=
    hdeltaRequested.trans (by simp [requestedBound, smallScale])
  have hdeltaCoupledLe : delta ≤ deltaCoupled :=
    hdeltaRequested.trans (by simp [requestedBound, smallScale])
  have hdataTarget : data.targetLoss = targetLoss := by
    rw [data.targetLoss_eq, hdataEta]
  have hdataSticky : data.stickyLoss = stickyLoss := by
    rw [data.stickyLoss_eq, hdataEta]
  have hrhoTiny : data.rho.1 ≤ 1 / 240000000000000000 := by
    rw [data.rho_eq_power]
    exact hrhoSmall delta hdelta hdeltaRhoLe
  have hrhoCoupledTiny : data.rho.1 ≤
      1 / (pureWZ2CoupledConflictConstant *
        pureWZ2CoupledScaleRequirement) := by
    rw [data.rho_eq_power]
    exact hcoupledSmall delta hdelta hdeltaCoupledLe
  have hcommonSmall : Kakeya.realRpowENN delta
        (4 * (data.eta / 2) - data.targetLoss - data.targetLoss -
          (1 + epsilon) * data.stickyLoss) ≤
      ENNReal.ofReal (1 / 400000 : ℝ) := by
    rw [hdataEta, hdataTarget, hdataSticky]
    simpa [Kakeya.realRpowENN] using
      ENNReal.ofReal_mono (hcommon delta hdelta hdeltaCommonLe)
  have hderivative :
      ∀ z ∈ Set.Icc data.scaleData.slabLeft data.scaleData.slabRight,
        data.scaleData.slabRight - data.scaleData.slabLeft ≤
          |deriv data.globalSlope z| := by
    have rule := lemma66 delta hdelta hdeltaLemma66Le
    rw [← hdataEta] at rule
    rcases data.toLemma66PreparedSlab_coordinates with ⟨left, right, slope⟩
    simpa only [left, right, slope] using rule data.toLemma66PreparedSlab
  have hdeltaRhoSq : delta ≤ data.rho.1 ^ 2 := by
    rw [data.rho_eq_power]
    have hpower : Real.rpow delta 1 ≤
        Real.rpow delta (2 * epsilon) :=
      Real.rpow_le_rpow_of_exponent_ge
        (y := (1 : ℝ)) (z := 2 * epsilon) hdelta
          data.cfg.extremal.delta_le_one (by linarith)
    have hrpowSq : Real.rpow delta (2 * epsilon) =
        (Real.rpow delta epsilon) ^ 2 := by
      calc
        Real.rpow delta (2 * epsilon) =
            Real.rpow delta (epsilon + epsilon) := by congr 1 <;> ring
        _ = Real.rpow delta epsilon * Real.rpow delta epsilon :=
          Real.rpow_add hdelta _ _
        _ = (Real.rpow delta epsilon) ^ 2 := by ring
    calc
      delta = Real.rpow delta 1 := (Real.rpow_one delta).symm
      _ ≤ Real.rpow delta (2 * epsilon) := hpower
      _ = (Real.rpow delta epsilon) ^ 2 := hrpowSq
  have hdeltaRhoEight : delta ≤ data.rho.1 ^ 8 := by
    rw [data.rho_eq_power]
    have hpower : Real.rpow delta 1 ≤
        Real.rpow delta (8 * epsilon) :=
      Real.rpow_le_rpow_of_exponent_ge
        (y := (1 : ℝ)) (z := 8 * epsilon) hdelta
          data.cfg.extremal.delta_le_one (by linarith)
    have hrpowEight : Real.rpow delta (8 * epsilon) =
        (Real.rpow delta epsilon) ^ 8 := by
      exact (rpow_nat_pow hdelta epsilon 8).symm.trans <| by
        congr 1 <;> ring
    calc
      delta = Real.rpow delta 1 := (Real.rpow_one delta).symm
      _ ≤ Real.rpow delta (8 * epsilon) := hpower
      _ = (Real.rpow delta epsilon) ^ 8 := hrpowEight
  exact ⟨delta, hdelta, hdeltaBound', ⟨{
    data := data
    sigma_pos := critical.sigma_pos
    epsilon_pos := hepsilon
    eta := eta
    eta_eq := hdataEta.symm
    eta_pos := heta
    eta_budget := hetaBudget
    delta_small := hdeltaSmall
    rho_tiny := hrhoTiny
    rho_coupled_tiny := hrhoCoupledTiny
    delta_le_rho_sq := hdeltaRhoSq
    delta_le_rho_eight := hdeltaRhoEight
    common_y_small := by simpa [hdataEta] using hcommonSmall
    derivative_lower := hderivative
  }, rfl⟩⟩

/-- Compatibility wrapper using the original maximal internal exponent. -/
theorem pureWZ2_lemma31_derivative_assembly_of_scale_producer
    (sigma epsilon : ℝ)
    (scaleProducer : ∀ eta deltaBound : ℝ,
      0 < eta → 1000 * eta ≤ epsilon * sigma ^ 2 →
      0 < deltaBound →
        ∃ delta : ℝ, 0 < delta ∧ delta ≤ deltaBound ∧
          ∃ data : PureWZ2Lemma31ScaleAssembly sigma epsilon delta,
            data.eta = eta)
    (critical : PureWZ2CriticalPackage sigma)
    (deltaBound : ℝ)
    (hepsilon : 0 < epsilon) (hepsilonEighth : epsilon ≤ 1 / 8)
    (hdeltaBound : 0 < deltaBound) :
    ∃ delta : ℝ, 0 < delta ∧ delta ≤ deltaBound ∧
      ∃ data : PureWZ2Lemma31DerivativeAssembly sigma epsilon delta,
        data.eta = epsilon * sigma ^ 2 / 2000 := by
  let eta := epsilon * sigma ^ 2 / 2000
  have heta : 0 < eta := by
    dsimp only [eta]
    exact div_pos (mul_pos hepsilon (sq_pos_of_pos critical.sigma_pos))
      (by norm_num)
  have hselectedEtaBudget : 1000 * eta ≤ epsilon * sigma ^ 2 := by
    dsimp only [eta]
    nlinarith [mul_pos hepsilon (sq_pos_of_pos critical.sigma_pos)]
  rcases pureWZ2_lemma31_derivative_assembly_with_eta_of_scale_producer
      sigma epsilon eta
      (scaleProducer := fun requestedBound hrequestedBound =>
        scaleProducer eta requestedBound heta hselectedEtaBudget hrequestedBound)
      critical deltaBound hepsilon hepsilonEighth heta hselectedEtaBudget hdeltaBound with
    ⟨delta, hdelta, hdeltaBound', data, _⟩
  exact ⟨delta, hdelta, hdeltaBound', data, ‹data.eta = eta›⟩

end Kakeya.Assouad
end
