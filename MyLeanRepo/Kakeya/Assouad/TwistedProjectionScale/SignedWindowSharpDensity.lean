import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.GridOSBoundedOneScaleFromBlock
import MyLeanRepo.Kakeya.Assouad.AbsorptionHelpers

/-!
# Lemma 7.12 with source density δ^η and retained density δ^(4η)

The positive-window theorem retains δ^(3η) by choosing its OS grid with
half the previous loss.  Here positiveEta = 4η/3, so its output is δ^(4η).
The gap positiveEta - η pays for the half-window selection.  All cutoffs
are selected before the runtime family, shading, and slope.
-/

namespace Kakeya.Assouad

/-- The full normalized parameter one-step contract with the paper's density
exponents.  This still assumes a vertical chart and parameter Frostman. -/
def GridOSBoundedOneScaleSharpInput : Prop :=
  ∀ epsilon rhoMax : ℝ,
    0 < epsilon →
    epsilon < 1 / 100 →
    0 < rhoMax →
    rhoMax ≤ 1 →
    1 / 100 ≤ rhoMax →
      ∃ etaMax : ℝ,
        0 < etaMax ∧
        etaMax ≤ epsilon ∧
        ∀ eta : ℝ,
          0 < eta →
          eta ≤ etaMax →
            ∃ delta₀ : ℝ,
              0 < delta₀ ∧
              delta₀ < 1 ∧
              ∀ delta : ℝ,
                0 < delta →
                delta ≤ delta₀ →
                ∀ F : Kakeya.Streamlined.TubeFamily delta,
                  F.Nonempty →
                  IsInVerticalChart F →
                  (∀ i : Fin F.card,
                    |(tubeParams i).a| ≤ 12 ∧
                      |(tubeParams i).b| ≤ 12 ∧
                      |(tubeParams i).c| ≤ 2 ∧
                      |(tubeParams i).d| ≤ 2) →
                  ∀ C : ENNReal,
                    1 ≤ C →
                    C ≠ ⊤ →
                    C ≤ Kakeya.realRpowENN delta (-eta) →
                    TubeParameterFrostmanBound F C →
                    ∀ Y : Kakeya.Streamlined.TubeShading F,
                      Y.IsLambdaDense
                        (Kakeya.realRpowENN delta eta) →
                      IsInSlopeWindow Y →
                      ∀ f : SlopeFunction,
                        f.IsNonsingular →
                        f 0 = 0 →
                          ∃ rho : ℝ,
                            Real.rpow delta
                                (1 - epsilon ^ 2) < rho ∧
                            rho ≤ rhoMax ∧
                            ∃ Z : Kakeya.Streamlined.TubeShading F,
                              IsSubshading Z Y ∧
                              Z.IsLambdaDense
                                (Kakeya.realRpowENN delta (4 * eta)) ∧
                              MeasureTheory.volume (twistedUnion Z f) ≥
                                Kakeya.realRpowENN
                                    (delta / rho) epsilon *
                                  MeasureTheory.volume
                                    (Metric.cthickening rho
                                      (twistedUnion Z f))

/-- Pay for the half-window choice from the improved positive-window density. -/
theorem grid_os_bounded_one_scale_sharp_from_positive
    (hPositive : PositiveWindowParameterFrostmanScaleWithDensityStatement 3)
    (hHolder : CompactAssignedCinematicHolderFromVerticalChartStatement)
    (hPYZ : PYZInput) : GridOSBoundedOneScaleSharpInput := by
  intro epsilon rhoMax hepsilon hepsilonOne hrhoMax hrhoMaxOne hrhoMaxLower
  obtain ⟨etaMax, hetaMax, hetaMaxEpsilon, hPositiveEta⟩ :=
    hPositive hHolder hPYZ epsilon rhoMax hepsilon hepsilonOne
      hrhoMax hrhoMaxOne hrhoMaxLower
  refine ⟨3 * etaMax / 4, by positivity, by linarith, ?_⟩
  intro sourceEta hsourceEta hsourceMax
  let eta := 4 * sourceEta / 3
  have heta : 0 < eta := by dsimp [eta]; positivity
  have hetaMax' : eta ≤ etaMax := by dsimp [eta]; linarith
  have hgap : 0 < eta - sourceEta := by dsimp [eta]; linarith
  have houtput : 3 * eta = 4 * sourceEta := by dsimp [eta]; ring
  obtain ⟨deltaPositive, hdp, hdp1, hPositiveAt⟩ := hPositiveEta eta heta hetaMax'
  obtain ⟨deltaAbsorb, hda, _, hAbsorb⟩ :=
    exists_delta_realRpowENN_bound (2 : ENNReal) (by norm_num) hgap
  refine ⟨min deltaPositive deltaAbsorb, lt_min hdp hda,
    (min_le_left _ _).trans_lt hdp1, ?_⟩
  intro delta hdelta hsmall F hn hv hp C hC hCtop hCb hF Y hdense hw f hf h0
  have hdp' : delta ≤ deltaPositive := hsmall.trans (min_le_left _ _)
  have hda' : delta ≤ deltaAbsorb := hsmall.trans (min_le_right _ _)
  have hd1 : delta ≤ 1 := (hdp'.trans_lt hdp1).le
  have hCb' : C ≤ Kakeya.realRpowENN delta (-eta) :=
    hCb.trans (ENNReal.ofReal_le_ofReal
      (Real.rpow_le_rpow_of_exponent_ge hdelta hd1 (by linarith)))
  have htwo : (2 : ENNReal) * Kakeya.realRpowENN delta eta ≤
      Kakeya.realRpowENN delta sourceEta := by
    calc
      _ ≤ Kakeya.realRpowENN delta (-(eta - sourceEta)) *
          Kakeya.realRpowENN delta eta :=
        mul_le_mul_left (hAbsorb delta hdelta hda') _
      _ = _ := by
        rw [← realRpowENN_add hdelta]
        congr 1
        ring
  obtain ⟨sign, hsign, Yhalf, hsub, hmass, hwindow⟩ :=
    half_window_mass_selection F Y hw
  have hhalfDense : Yhalf.IsLambdaDense (Kakeya.realRpowENN delta eta) := by
    have hhalfTwo : (1 / 2 : ENNReal) * 2 = 1 := by
      rw [one_div, ENNReal.inv_mul_cancel (by norm_num) (by norm_num)]
    calc
      Kakeya.realRpowENN delta eta * F.toBodyFamily.mass =
          ((1 / 2 : ENNReal) * 2) *
            (Kakeya.realRpowENN delta eta * F.toBodyFamily.mass) := by rw [hhalfTwo, one_mul]
      _ = (1 / 2 : ENNReal) *
          ((2 * Kakeya.realRpowENN delta eta) * F.toBodyFamily.mass) := by ring
      _ ≤ (1 / 2 : ENNReal) *
          (Kakeya.realRpowENN delta sourceEta * F.toBodyFamily.mass) := by gcongr
      _ ≤ (1 / 2 : ENNReal) * Y.mass := mul_le_mul_right hdense _
      _ ≤ Yhalf.mass := hmass
  rcases hsign with rfl | rfl
  · have hpositive : Yhalf.union ⊆ horizontalSlab 0 1 := by simpa using hwindow
    obtain ⟨rho, hrl, hru, Z, hz, hzd, hproj⟩ :=
      hPositiveAt delta hdelta hdp' F hn hv hp C hC hCtop hCb' hF
        Yhalf hhalfDense hpositive f hf h0
    rw [houtput] at hzd
    exact ⟨rho, hrl, hru, Z, fun i => (hz i).trans (hsub i), hzd, hproj⟩
  · have hnegative : Yhalf.union ⊆ horizontalSlab (-1) 0 := by
      simpa only [if_neg (by norm_num : (-1 : ℝ) ≠ 1)] using hwindow
    obtain ⟨reflectedFamily, reflectedShading, hnonempty, _hbase, _hdistinct,
        hvertical, hparams, hfrostman, hdensity, hwindow', hpullback⟩ :=
      section7_vertical_reflection F Yhalf
    have hfReflected := (reflected_slope_cinematic f hf).1
    have hf0 : f.reflected 0 = 0 := by simpa [SlopeFunction.reflected] using h0
    obtain ⟨rho, hrl, hru, W, hwsub, hwd, hproj⟩ :=
      hPositiveAt delta hdelta hdp' reflectedFamily (hnonempty hn)
        (hvertical hv) (hparams hp) C hC hCtop hCb' (hfrostman C hF)
        reflectedShading (hdensity _ hhalfDense) (hwindow' hnegative)
        f.reflected hfReflected hf0
    obtain ⟨Z, hzsub, hzdensity, hvolume⟩ := hpullback W hwsub
    have heq := hvolume f
    rw [heq.1, heq.2 rho] at hproj
    rw [houtput] at hwd
    exact ⟨rho, hrl, hru, Z, fun i => (hzsub i).trans (hsub i),
      hzdensity _ hwd, hproj⟩

/-- The sharper density theorem supplies the existing finite-iteration API. -/
theorem GridOSBoundedOneScaleSharpInput.toLegacy
    (h : GridOSBoundedOneScaleSharpInput) : GridOSBoundedOneScaleInput := by
  intro epsilon rhoMax he he1 hr hr1 hrl
  obtain ⟨etaMax, hm, hme, hEta⟩ := h epsilon rhoMax he he1 hr hr1 hrl
  refine ⟨etaMax, hm, hme, ?_⟩
  intro eta heta hetam
  obtain ⟨delta₀, hd, hd1, hmain⟩ := hEta eta heta hetam
  refine ⟨delta₀, hd, hd1, ?_⟩
  intro delta hdelta hsmall F hn hv hp C hC hCtop hCb hF Y hy hw f hf h0
  have hy' : Y.IsLambdaDense (Kakeya.realRpowENN delta eta) :=
    (mul_le_mul_left (ENNReal.ofReal_le_ofReal
      (Real.rpow_le_rpow_of_exponent_ge hdelta (hsmall.trans_lt hd1).le
        (by linarith : eta / 2 ≤ eta))) _).trans hy
  exact hmain delta hdelta hsmall F hn hv hp C hC hCtop hCb hF Y hy' hw f hf h0

end Kakeya.Assouad
