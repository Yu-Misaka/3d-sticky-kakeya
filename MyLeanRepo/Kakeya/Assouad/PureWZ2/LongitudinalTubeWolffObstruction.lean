import MyLeanRepo.Kakeya.Assouad.PureWZ2.LongitudinalTubeGridWolff
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LongitudinalTubeGridDistinct
import MyLeanRepo.Kakeya.Assouad.PureWZ2.OrdinaryTubeWolff
import MyLeanRepo.Kakeya.Assouad.ConstantAbsorption

/-!
# The ordinary longitudinal-model obstruction, with f(0)=0

The slope is the fixed normalized function f(z)=z. The fine unit segments
are in the vertical chart, but have varying center heights. Their ordinary
capsule Tube Wolff constant is absolute, while their twisted area is at most
24 sqrt(delta). This concerns the literal unit-segment coarse-test model;
no CWA condition is asserted and the common-height terminal is unaffected.
-/

noncomputable section
open MeasureTheory Set
namespace Kakeya.Assouad

theorem longitudinalTubeGrid_sqrt_scale {n : ℕ} (hn : 0 < n) :
    Real.sqrt (planarTubeGridScale (n*n)) = planarTubeGridMesh n := by
  have hsq := longitudinalTubeGrid_scale_square hn
  have hroot := Real.sq_sqrt (planarTubeGridScale_pos (Nat.mul_pos hn hn)).le
  nlinarith [planarTubeGridMesh_pos hn, Real.sqrt_nonneg (planarTubeGridScale (n*n))]

theorem longitudinalTubeGridScale_arbitrarily_small {cutoff : ℝ} (hcutoff : 0 < cutoff) :
    ∃ n : ℕ, 0 < n ∧ planarTubeGridScale (n*n) < cutoff := by
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hcutoff
  let n := m + 1
  have hn : 0 < n := by dsimp [n]; omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  refine ⟨n, hn, ?_⟩
  calc
    _ ≤ planarTubeGridMesh n := longitudinalTubeGrid_scale_le_width hn
    _ ≤ 1 / (n : ℝ) := by
      apply (le_div_iff₀ hnR).2
      rw [planarTubeGridMesh_mul n hn]
      norm_num
    _ < cutoff := by simpa only [n, Nat.cast_add, Nat.cast_one] using hm

/-- All hypotheses of the normalized ordinary Tube Wolff-only claim hold,
even in the bounded vertical chart, on a finite essentially distinct family. -/
theorem exists_normalized_ordinary_tubeWolff_longitudinal_counterexample
    {eta cutoff : ℝ} (heta : 0 < eta) (hcutoff : 0 < cutoff) :
    ∃ delta : ℝ, 0 < delta ∧ delta ≤ cutoff ∧
      ∃ (F : Kakeya.Streamlined.TubeFamily delta)
        (Y : Kakeya.Streamlined.TubeShading F) (f : SlopeFunction),
        F.Nonempty ∧ F.IsInUnitBall ∧ WZ2PaperOrdinaryIsEssentiallyDistinct F ∧
        WZ1PaperIsLineClass F ∧ HasBoundedBase F 4 ∧
        OrdinaryTubeWolffVolumeBound F (Kakeya.realRpowENN delta (-eta)) ∧
        Y.IsLambdaDense (Kakeya.realRpowENN delta eta) ∧ IsInSlopeWindow Y ∧
        f.IsNonsingular ∧ f 0 = 0 ∧
        volume (twistedUnion Y f) < Kakeya.realRpowENN delta (1 / 4) := by
  obtain ⟨wolffScale, hwolffScale, _, hwolff⟩ :=
    exists_delta_realRpowENN_bound (1152921504606846976 : ENNReal) (by norm_num) heta
  obtain ⟨areaScale, hareaScale, _, harea⟩ :=
    exists_delta_mul_rpow_le_rpow 24 (by norm_num)
      (show (3 / 8 : ℝ) < 1 / 2 by norm_num)
  obtain ⟨n, hn, hscale⟩ := longitudinalTubeGridScale_arbitrarily_small
    (lt_min hcutoff (lt_min hwolffScale hareaScale))
  let delta := planarTubeGridScale (n*n)
  have hdelta : 0 < delta := planarTubeGridScale_pos (Nat.mul_pos hn hn)
  have hdeltaOne : delta < 1 := (planarTubeGridScale_le (Nat.mul_pos hn hn)).trans_lt (by norm_num)
  have hcut : delta ≤ cutoff := hscale.le.trans (min_le_left _ _)
  have hwcut : delta ≤ wolffScale := hscale.le.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hacut : delta ≤ areaScale := hscale.le.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hC := hwolff _ hdelta hwcut
  have hCOne : (1 : ENNReal) ≤ Kakeya.realRpowENN delta (-eta) :=
    (by norm_num : (1 : ENNReal) ≤ 1152921504606846976).trans hC
  have htw : TubeWolffBound (longitudinalTubeGrid n) (Kakeya.realRpowENN delta (-eta)) := by
    intro r hdr hrOne T
    exact (longitudinalTubeGrid_tubeWolff hn r hdr hrOne T).trans (by gcongr)
  have hdense : (longitudinalTubeGridShading n).IsLambdaDense (Kakeya.realRpowENN delta eta) := by
    have hpow : Kakeya.realRpowENN delta eta ≤ 1 := by
      exact (ENNReal.ofReal_mono (Real.rpow_le_one hdelta.le hdeltaOne.le heta.le)).trans_eq ENNReal.ofReal_one
    exact (mul_le_mul_left hpow _).trans (longitudinalTubeGridShading_dense n)
  have hareaBound : volume (twistedUnion (longitudinalTubeGridShading n) (offsetObstructionSlope 0)) <
      Kakeya.realRpowENN delta (1 / 4) := by
    have hbound : 24 * planarTubeGridMesh n ≤ Real.rpow delta (3 / 8) := by
      rw [← longitudinalTubeGrid_sqrt_scale hn]
      calc
        _ = 24 * Real.rpow delta (1 / 2) := congrArg (24 * ·) (Real.sqrt_eq_rpow _)
        _ ≤ _ := harea _ hdelta hacut
    have hstrict := Real.rpow_lt_rpow_of_exponent_gt hdelta hdeltaOne
      (show (1 / 4 : ℝ) < 3 / 8 by norm_num)
    have hstrictENN : ENNReal.ofReal (Real.rpow delta (3 / 8)) < Kakeya.realRpowENN delta (1 / 4) :=
      (ENNReal.ofReal_lt_ofReal_iff (Real.rpow_pos_of_pos hdelta _)).2 hstrict
    exact ((longitudinalTubeGrid_projection_volume hn).trans (ENNReal.ofReal_mono hbound)).trans_lt hstrictENN
  exact ⟨delta, hdelta, hcut, longitudinalTubeGrid n, longitudinalTubeGridShading n,
    offsetObstructionSlope 0, longitudinalTubeGrid_nonempty hn,
    longitudinalTubeGrid_in_unitBall hn, longitudinalTubeGrid_ordinary_distinct hn,
    longitudinalTubeGrid_lineClass hn, longitudinalTubeGrid_boundedBase hn,
    htw.to_ordinaryVolume hdelta hCOne, hdense, longitudinalTubeGridShading_window hn,
    offsetObstructionSlope_nonsingular 0, by simp, hareaBound⟩

/-- The literal ordinary capsule claim after only imposing f(0)=0 and a
vertical chart; longitudinal centers are still unrestricted. -/
def PureWZ2NormalizedOrdinaryTubeWolffProjectionStatement : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon →
    ∃ eta cutoff : ℝ, 0 < eta ∧ 0 < cutoff ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ cutoff →
        ∀ F : Kakeya.Streamlined.TubeFamily delta,
          F.Nonempty → F.IsInUnitBall → WZ2PaperOrdinaryIsEssentiallyDistinct F →
          IsInVerticalChart F →
          OrdinaryTubeWolffVolumeBound F (Kakeya.realRpowENN delta (-eta)) →
          ∀ Y : Kakeya.Streamlined.TubeShading F,
            Y.IsLambdaDense (Kakeya.realRpowENN delta eta) → IsInSlopeWindow Y →
            ∀ f : SlopeFunction, f.IsNonsingular → f 0 = 0 →
              Kakeya.realRpowENN delta epsilon ≤ volume (twistedUnion Y f)

theorem not_pureWZ2NormalizedOrdinaryTubeWolffProjectionStatement :
    ¬ PureWZ2NormalizedOrdinaryTubeWolffProjectionStatement := by
  intro h
  obtain ⟨eta, cutoff, heta, hcutoff, hmain⟩ := h (1 / 4) (by norm_num)
  obtain ⟨delta, hd, hcut, F, Y, f, hn, hb, he, hl, hbase, htw, hy, hw, hf, hz, harea⟩ :=
    exists_normalized_ordinary_tubeWolff_longitudinal_counterexample heta hcutoff
  exact (not_lt_of_ge (hmain delta hd hcut F hn hb he hl.vertical htw Y hy hw f hf hz)) harea

end Kakeya.Assouad
end
