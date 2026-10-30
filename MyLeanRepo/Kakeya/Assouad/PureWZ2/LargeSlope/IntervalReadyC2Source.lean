import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.Node6FixedLemma31ScaleAssembly
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.Lemma66PrescribedInterval
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.Lemma66NormalizedInterval

/-!
# A C2 source prepared before any interval is specified

Certified Proposition 6.2 preconditioning gives a global fine multiplicity
cap. The stronger historical source also retains a global frame certificate.
The prescribed-interval endpoint now needs only the cap before the interval:
the normalized Lemma 6.6 constructs its frame on each actual slab.
-/

noncomputable section
open MeasureTheory Set
namespace Kakeya.Assouad

structure PureWZ2IntervalReadyC2Source (sigma loss capLoss delta : ℝ) where
  cfg : PureWZ2C2GrainConfiguration sigma loss delta
  frame : PureWZ2FrameNormalCompatibility cfg
  fine_cap : ∀ p, (cfg.shading.pointMultiplicity p : ENNReal) ≤
    Kakeya.realRpowENN delta (2 - sigma - capLoss) * cfg.family.enncard

theorem pureWZ2_interval_ready_c2_source
    {logExponent : ℕ}
    (hc2grains : PureWZ2C2GrainsFromCriticalStatement)
    (certifiedProvider : PureWZ2Node6FixedScaleCriticalAt logExponent)
    (sigma : ℝ) (critical : PureWZ2CriticalPackage sigma)
    (loss capLoss deltaBound : ℝ)
    (hloss : 0 < loss) (hcapLoss : 0 < capLoss) (hdeltaBound : 0 < deltaBound) :
    ∃ delta : ℝ, 0 < delta ∧ delta ≤ deltaBound ∧
      Nonempty (PureWZ2IntervalReadyC2Source sigma loss capLoss delta) := by
  let smallLoss := min (loss / 2) (min (sigma / 64) (1 / 4))
  have hsmall : 0 < smallLoss := by
    dsimp [smallLoss]
    positivity [critical.sigma_pos]
  have hsmallLoss : smallLoss ≤ loss := (min_le_left _ _).trans (by linarith)
  have hsmallSigma : smallLoss ≤ sigma / 64 := (min_le_right _ _).trans (min_le_left _ _)
  have hsmallQuarter : smallLoss ≤ 1 / 4 := (min_le_right _ _).trans (min_le_right _ _)
  let P : ∀ {sourceLoss delta : ℝ}, PureWZ2C2GrainConfiguration sigma sourceLoss delta → Prop :=
    fun {sourceLoss delta} cfg => ∀ p, (cfg.shading.pointMultiplicity p : ENNReal) ≤
      Kakeya.realRpowENN delta (2 - sigma - capLoss) * cfg.family.enncard
  have sourceProvider : ∀ sourceLoss localBound : ℝ,
      0 < sourceLoss → 0 < localBound →
        ∃ delta : ℝ, 0 < delta ∧ delta ≤ localBound ∧
          ∃ cfg : PureWZ2C2GrainConfiguration sigma sourceLoss delta, P cfg := by
    intro sourceLoss localBound hsourceLoss hlocalBound
    exact pureWZ2_c2_source_with_fine_cap hc2grains certifiedProvider sigma critical
      sourceLoss capLoss localBound hsourceLoss hcapLoss hlocalBound
  obtain ⟨delta, hdelta, hcut, sqrtData, hsourceCap⟩ :=
    pureWZ2_node6_fixed_sqrt_assembly_with_source_property sigma sourceProvider
      certifiedProvider critical smallLoss deltaBound hsmall
      (by linarith) (by linarith [critical.sigma_pos]) hdeltaBound
  let cfg := sqrtData.cfg.mono_loss hdelta sqrtData.cfg.extremal.delta_le_one hsmall.le hsmallLoss
  have hframe : PureWZ2FrameNormalCompatibility cfg := by
    intro frameSlope p hclose
    exact sqrtData.frameNormalCompatibility frameSlope p hclose
  have hfamily : sqrtData.cfg.family = sqrtData.sourceCfg.family := by
    rw [sqrtData.cfg_eq]
    exact sqrtData.zeroData.configuration_family
  have hcap : ∀ p, (cfg.shading.pointMultiplicity p : ENNReal) ≤
      Kakeya.realRpowENN delta (2 - sigma - capLoss) * cfg.family.enncard := by
    intro p
    have hle : sqrtData.cfg.shading.pointMultiplicity p ≤
        sqrtData.sourceCfg.shading.pointMultiplicity p := by
      rw [sqrtData.cfg_eq]
      exact sqrtData.zeroData.configuration_pointMultiplicity_le_source p
    change (sqrtData.cfg.shading.pointMultiplicity p : ENNReal) ≤
      Kakeya.realRpowENN delta (2 - sigma - capLoss) * sqrtData.cfg.family.enncard
    have hcard : sqrtData.cfg.family.enncard = sqrtData.sourceCfg.family.enncard :=
      congrArg (fun F : Kakeya.Streamlined.TubeFamily delta => F.enncard) hfamily
    rw [hcard]
    exact (show (sqrtData.cfg.shading.pointMultiplicity p : ENNReal) ≤
      (sqrtData.sourceCfg.shading.pointMultiplicity p : ENNReal) by exact_mod_cast hle).trans
        (hsourceCap p)
  exact ⟨delta, hdelta, hcut, ⟨⟨cfg, hframe, hcap⟩⟩⟩

/-- A strengthened Proposition 6.4 output supports every prescribed interval.
The statement has no frame, multiplicity or whole-cell hypotheses for the
caller to prove. Its slab mass is explicitly proportional to delta^2*#T. -/
def PureWZ2C2PrescribedIntervalsStatement : Prop :=
  ∀ sigma : ℝ, PureWZ2CriticalPackage sigma →
    ∀ epsilon eta deltaBound : ℝ,
    0 < epsilon → epsilon ≤ 1 / 2 →
    0 < eta → 2000 * eta ≤ epsilon * sigma ^ 2 → 0 < deltaBound →
    ∃ delta : ℝ, 0 < delta ∧ delta ≤ deltaBound ∧
      ∃ (cfg : PureWZ2C2GrainConfiguration sigma (eta / 8) delta) (f : SlopeFunction),
        (∀ z ∈ Set.Icc (-1 : ℝ) 1, f z = cfg.globalGrains.slope z) ∧ f.IsNormalized ∧
        ∀ a b : ℝ, -1 ≤ a → a < b → b ≤ 1 →
          Real.rpow delta (1 / 2) ≤ b - a → b - a ≤ Real.rpow delta epsilon →
          ENNReal.ofReal (Real.pi / 4) * Kakeya.realRpowENN delta (eta / 16 + 2) *
              cfg.family.enncard * ENNReal.ofReal (b - a) ≤
            paperShadedMassInSlab cfg.shading a b →
          CanCoverByBalls (cfg.shading.union ∩ horizontalSlab a b) (b - a)
            (Kakeya.realRpowENN delta (-(eta / 16)) *
              Kakeya.realRpowENN (b - a) (-2 + sigma)) →
          ∀ z ∈ Set.Icc a b, b - a ≤ |deriv f z|

theorem pureWZ2_c2_source_with_prescribed_intervals
    {logExponent : ℕ}
    (hc2grains : PureWZ2C2GrainsFromCriticalStatement)
    (certifiedProvider : PureWZ2Node6FixedScaleCriticalAt logExponent) :
    PureWZ2C2PrescribedIntervalsStatement := by
  intro sigma critical epsilon eta deltaBound hepsilon hepsilonHalf heta hbudget hdeltaBound
  obtain ⟨cutoff, hcutoff, _, derivative⟩ :=
    pure_wz2_lemma66_normalized_interval sigma epsilon eta critical.sigma_pos
      critical.sigma_lt_one hepsilon hepsilonHalf heta hbudget
  obtain ⟨delta, hdelta, hbound, cfg, hcap⟩ :=
    pureWZ2_c2_source_with_fine_cap hc2grains certifiedProvider sigma critical
      (eta / 8) (eta / 8192) (min deltaBound cutoff)
      (by positivity) (by positivity) (lt_min hdeltaBound hcutoff)
  obtain ⟨globalized⟩ := cfg.globalGrains.globalizedSlope
  refine ⟨delta, hdelta, hbound.trans (min_le_left _ _), cfg,
    globalized.slope, globalized.eq_on, globalized.normalized, ?_⟩
  intro a b ha hab hb hlower hupper hmass hcover
  exact derivative delta hdelta (hbound.trans (min_le_right _ _))
    cfg globalized.slope globalized.eq_on globalized.normalized
    a b ha hab hb hlower hupper hmass hcover (fun p _ => hcap p)

end Kakeya.Assouad
end
