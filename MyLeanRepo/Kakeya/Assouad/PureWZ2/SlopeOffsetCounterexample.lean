import MyLeanRepo.Kakeya.Assouad.PureWZ2.PlanarTubeGridWolff
import MyLeanRepo.Kakeya.Assouad.ConstantAbsorption

/-!
# A finite counterexample to a uniform arbitrary-offset Tube Wolff estimate

For every loss eta and every positive scale cutoff, the planar grid gives
ordinary, essentially distinct unit tubes in the unit ball with Tube Wolff
error delta^(-eta), full shading, and a nonsingular slope f(z)=s+z. Taking
s=delta^(-1/2) makes the twisted area at most 32*sqrt(delta), and hence
strictly less than delta^(1/4) at sufficiently small scales.

This concerns Tube Wolff alone. No convex Wolff hypothesis is asserted.
The normalized projection theorems, which require f(0)=0, are unaffected.
-/

noncomputable section
open MeasureTheory Set
namespace Kakeya.Assouad

def planarTubeGridOffset (n : ℕ) : ℝ := (Real.sqrt (planarTubeGridScale n))⁻¹

theorem planarTubeGridOffset_one_le {n : ℕ} (hn : 0 < n) :
    1 ≤ planarTubeGridOffset n := by
  have hpos := Real.sqrt_pos_of_pos (planarTubeGridScale_pos hn)
  have hsq := Real.sq_sqrt (planarTubeGridScale_pos hn).le
  have hsmall : Real.sqrt (planarTubeGridScale n) ≤ 1 := by
    nlinarith [planarTubeGridScale_le hn]
  change 1 ≤ (Real.sqrt (planarTubeGridScale n))⁻¹
  rw [← one_div]
  exact (le_div_iff₀ hpos).2 (by simpa using hsmall)

theorem planarTubeGrid_projection_sqrt {n : ℕ} (hn : 0 < n) :
    volume (twistedUnion (planarTubeGridShading n (planarTubeGridOffset n))
      (offsetObstructionSlope (planarTubeGridOffset n))) ≤
        ENNReal.ofReal (32 * Real.sqrt (planarTubeGridScale n)) := by
  have hpos := Real.sqrt_pos_of_pos (planarTubeGridScale_pos hn)
  have hsq := Real.sq_sqrt (planarTubeGridScale_pos hn).le
  have heq : 12 * planarTubeGridOffset n * planarTubeGridScale n +
      20 / planarTubeGridOffset n = 32 * Real.sqrt (planarTubeGridScale n) := by
    unfold planarTubeGridOffset
    field_simp [hpos.ne']
    nlinarith
  exact (planarTubeGrid_projection_volume hn (planarTubeGridOffset_one_le hn)).trans_eq
    (congrArg ENNReal.ofReal heq)

theorem planarTubeGridScale_arbitrarily_small {cutoff : ℝ} (hcutoff : 0 < cutoff) :
    ∃ n : ℕ, 0 < n ∧ planarTubeGridScale n < cutoff := by
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hcutoff
  refine ⟨m + 1, by omega, ?_⟩
  have hn : 0 < m + 1 := by omega
  have hnreal : (0 : ℝ) < (m + 1 : ℕ) := by exact_mod_cast hn
  have hscale : planarTubeGridScale (m + 1) = (1 / 4096) / ((m + 1 : ℕ) : ℝ) := by
    exact (eq_div_iff hnreal.ne').2 (planarTubeGridScale_mul (m + 1) hn)
  calc
    _ = (1 / 4096) / ((m + 1 : ℕ) : ℝ) := hscale
    _ ≤ 1 / ((m + 1 : ℕ) : ℝ) := div_le_div_of_nonneg_right (by norm_num) hnreal.le
    _ < cutoff := by simpa only [Nat.cast_add, Nat.cast_one] using hm

/-- The family, shading and slope are explicit; only the integer grid size is selected. -/
theorem exists_planarTubeGrid_slope_offset_counterexample
    {eta cutoff : ℝ} (heta : 0 < eta) (hcutoff : 0 < cutoff) :
    ∃ n : ℕ, 0 < n ∧ planarTubeGridScale n ≤ cutoff ∧
      TubeWolffBound (planarTubeGrid n (planarTubeGridOffset n))
        (Kakeya.realRpowENN (planarTubeGridScale n) (-eta)) ∧
      (planarTubeGridShading n (planarTubeGridOffset n)).IsLambdaDense
        (Kakeya.realRpowENN (planarTubeGridScale n) eta) ∧
      volume (twistedUnion (planarTubeGridShading n (planarTubeGridOffset n))
        (offsetObstructionSlope (planarTubeGridOffset n))) <
          Kakeya.realRpowENN (planarTubeGridScale n) (1 / 4) := by
  obtain ⟨wolffScale, hwolffScale, _, hwolff⟩ :=
    exists_delta_realRpowENN_bound (3865470566400 : ENNReal) (by norm_num) heta
  obtain ⟨areaScale, hareaScale, _, harea⟩ :=
    exists_delta_mul_rpow_le_rpow 32 (by norm_num)
      (show (3 / 8 : ℝ) < 1 / 2 by norm_num)
  obtain ⟨n, hn, hscale⟩ := planarTubeGridScale_arbitrarily_small
    (lt_min hcutoff (lt_min hwolffScale hareaScale))
  have hdelta := planarTubeGridScale_pos hn
  have hdeltaOne : planarTubeGridScale n < 1 := (planarTubeGridScale_le hn).trans_lt (by norm_num)
  have hcut : planarTubeGridScale n ≤ cutoff := hscale.le.trans (min_le_left _ _)
  have hwcut : planarTubeGridScale n ≤ wolffScale :=
    hscale.le.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hacut : planarTubeGridScale n ≤ areaScale :=
    hscale.le.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hC := hwolff _ hdelta hwcut
  refine ⟨n, hn, hcut, ?_, ?_, ?_⟩
  · intro r hdr hrOne T
    exact (planarTubeGrid_tubeWolff hn (planarTubeGridOffset_one_le hn) r hdr hrOne T).trans (by gcongr)
  · have hpow : Kakeya.realRpowENN (planarTubeGridScale n) eta ≤ 1 := by
      have h : Real.rpow (planarTubeGridScale n) eta ≤ 1 :=
        Real.rpow_le_one hdelta.le hdeltaOne.le heta.le
      exact (ENNReal.ofReal_mono h).trans_eq ENNReal.ofReal_one
    exact (mul_le_mul_left hpow _).trans (planarTubeGridShading_dense n (planarTubeGridOffset n))
  · have hbound : 32 * Real.sqrt (planarTubeGridScale n) ≤
        Real.rpow (planarTubeGridScale n) (3 / 8) := by
      calc
        _ = 32 * Real.rpow (planarTubeGridScale n) (1 / 2) :=
          congrArg (32 * ·) (Real.sqrt_eq_rpow _)
        _ ≤ _ := harea _ hdelta hacut
    have hstrict := Real.rpow_lt_rpow_of_exponent_gt hdelta hdeltaOne
      (show (1 / 4 : ℝ) < 3 / 8 by norm_num)
    have hstrictENN : ENNReal.ofReal (Real.rpow (planarTubeGridScale n) (3 / 8)) <
        Kakeya.realRpowENN (planarTubeGridScale n) (1 / 4) :=
      (ENNReal.ofReal_lt_ofReal_iff (Real.rpow_pos_of_pos hdelta _)).2 hstrict
    exact ((planarTubeGrid_projection_sqrt hn).trans (ENNReal.ofReal_mono hbound)).trans_lt hstrictENN

/-- A witness to failure even with the ordinary paper distinctness and unit-ball conventions. -/
theorem exists_ordinary_tubeWolff_slope_offset_counterexample
    {eta cutoff : ℝ} (heta : 0 < eta) (hcutoff : 0 < cutoff) :
    ∃ delta : ℝ, 0 < delta ∧ delta ≤ cutoff ∧
      ∃ (F : Kakeya.Streamlined.TubeFamily delta)
        (Y : Kakeya.Streamlined.TubeShading F) (f : SlopeFunction),
        F.Nonempty ∧ F.IsInUnitBall ∧ WZ2PaperOrdinaryIsEssentiallyDistinct F ∧
        WZ1PaperIsLineClass F ∧ HasBoundedBase F 4 ∧
        TubeWolffBound F (Kakeya.realRpowENN delta (-eta)) ∧
        Y.IsLambdaDense (Kakeya.realRpowENN delta eta) ∧ IsInSlopeWindow Y ∧
        f.IsNonsingular ∧ volume (twistedUnion Y f) < Kakeya.realRpowENN delta (1 / 4) := by
  obtain ⟨n, hn, hcut, hwolff, hdense, harea⟩ :=
    exists_planarTubeGrid_slope_offset_counterexample heta hcutoff
  have hs := planarTubeGridOffset_one_le hn
  exact ⟨planarTubeGridScale n, planarTubeGridScale_pos hn, hcut,
    planarTubeGrid n (planarTubeGridOffset n), planarTubeGridShading n (planarTubeGridOffset n),
    offsetObstructionSlope (planarTubeGridOffset n), planarTubeGrid_nonempty hn _,
    planarTubeGrid_in_unitBall hn hs, planarTubeGrid_ordinary_distinct hn hs,
    planarTubeGrid_lineClass hn hs, planarTubeGrid_boundedBase hn hs, hwolff, hdense,
    planarTubeGridShading_window hn _, offsetObstructionSlope_nonsingular _, harea⟩

/-- The unrestricted-offset ordinary Tube Wolff claim with uniform cutoffs. -/
def PureWZ2UnrestrictedTubeWolffProjectionStatement : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon →
    ∃ eta cutoff : ℝ, 0 < eta ∧ 0 < cutoff ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ cutoff →
        ∀ F : Kakeya.Streamlined.TubeFamily delta,
          F.Nonempty → F.IsInUnitBall → WZ2PaperOrdinaryIsEssentiallyDistinct F →
          TubeWolffBound F (Kakeya.realRpowENN delta (-eta)) →
          ∀ Y : Kakeya.Streamlined.TubeShading F,
            Y.IsLambdaDense (Kakeya.realRpowENN delta eta) → IsInSlopeWindow Y →
            ∀ f : SlopeFunction, f.IsNonsingular →
              Kakeya.realRpowENN delta epsilon ≤ volume (twistedUnion Y f)

theorem not_pureWZ2UnrestrictedTubeWolffProjectionStatement :
    ¬ PureWZ2UnrestrictedTubeWolffProjectionStatement := by
  intro h
  obtain ⟨eta, cutoff, heta, hcutoff, hmain⟩ := h (1 / 4) (by norm_num)
  obtain ⟨delta, hdelta, hcut, F, Y, f, hnonempty, hball, hdistinct,
    hline, hbase, hwolff, hdense, hwindow, hf, harea⟩ :=
    exists_ordinary_tubeWolff_slope_offset_counterexample heta hcutoff
  exact (not_lt_of_ge (hmain delta hdelta hcut F hnonempty hball hdistinct
    hwolff Y hdense hwindow f hf)) harea

end Kakeya.Assouad
end
