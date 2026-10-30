import MyLeanRepo.Kakeya.Assouad.PureWZ2.SlopeOffsetNormalization
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.Section6Absorption

/-!
# Uniform scalar budget for centering the actual terminal

For source loss a and cleanup loss b > 3a, one scale cutoff pays for the
slab, radius enlargement and the offset bound 1+|f(0)| <= delta^(-a).
The cutoff is fixed before the slope or configuration is supplied.
-/

noncomputable section
namespace Kakeya.Assouad

theorem exists_slopeOffset_normalization_budget
    (a b : ℝ) (ha : 0 < a) (hab : 3 * a < b) (hbOne : b ≤ 1) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ {delta : ℝ}, 0 < delta → delta ≤ delta₀ →
      ∀ s : ℝ, 1 + |s| ≤ Real.rpow delta (-a) →
        20736 * Real.rpow (12 * delta) b ≤
            slopeOffsetScale s ^ 2 * Real.rpow delta a ∧
        (slopeOffsetScale s ^ 2)⁻¹ * Real.rpow delta (-a) ≤
            Real.rpow (12 * delta) (-b) := by
  obtain ⟨delta₀, hd₀, hd₀One, hsmall⟩ :=
    exists_delta_constant_mul_power_le_power (3981312 : ENNReal) (by norm_num)
      (3 * a) b hab
  refine ⟨delta₀, hd₀, hd₀One, ?_⟩
  intro delta hdelta hcutoff s hs
  have hdOne := hcutoff.trans hd₀One
  have hp : 0 < Real.rpow delta a := Real.rpow_pos_of_pos hdelta a
  have hpb : 0 < Real.rpow (12 * delta) b :=
    Real.rpow_pos_of_pos (by positivity : 0 < 12 * delta) b
  have hk := slopeOffsetScale_pos s
  have hL : (1 + |s|) * Real.rpow delta a ≤ 1 := by
    calc
      _ ≤ Real.rpow delta (-a) * Real.rpow delta a := by gcongr
      _ = Real.rpow delta (-a + a) := (Real.rpow_add hdelta _ _).symm
      _ = 1 := by simp
  have hklower : Real.rpow delta a / 4 ≤ slopeOffsetScale s := by
    unfold slopeOffsetScale
    rw [← one_div]
    apply (le_div_iff₀ (by positivity)).2
    nlinarith
  have hscale : Real.rpow (12 * delta) b ≤ 12 * Real.rpow delta b := by
    calc
      _ = Real.rpow 12 b * Real.rpow delta b := Real.mul_rpow (by norm_num) hdelta.le
      _ ≤ Real.rpow 12 1 * Real.rpow delta b := by
        exact mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 12) hbOne)
          (Real.rpow_nonneg hdelta.le b)
      _ = _ := by simp
  have hsmallReal : 3981312 * Real.rpow delta b ≤ Real.rpow delta (3 * a) := by
    have h := hsmall hdelta hcutoff
    rw [Kakeya.realRpowENN, Kakeya.realRpowENN,
      ← show ENNReal.ofReal (3981312 : ℝ) = 3981312 by norm_num,
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3981312)] at h
    exact (ENNReal.ofReal_le_ofReal_iff (Real.rpow_nonneg hdelta.le _)).mp h
  have hmass : Real.rpow delta (3 * a) / 16 ≤
      slopeOffsetScale s ^ 2 * Real.rpow delta a := by
    calc
      _ = (Real.rpow delta a / 4) ^ 2 * Real.rpow delta a := by
        have hpow : Real.rpow delta (3 * a) =
            Real.rpow delta a * Real.rpow delta a * Real.rpow delta a := by
          calc
            _ = Real.rpow delta ((a + a) + a) := by congr 1; ring
            _ = Real.rpow delta (a + a) * Real.rpow delta a := Real.rpow_add hdelta _ _
            _ = _ := congrArg (fun x : ℝ => x * Real.rpow delta a)
              (Real.rpow_add hdelta a a)
        rw [hpow]
        ring
      _ ≤ _ := by gcongr
  have hbudget : 20736 * Real.rpow (12 * delta) b ≤
      slopeOffsetScale s ^ 2 * Real.rpow delta a := by
    calc
      _ ≤ 248832 * Real.rpow delta b := by nlinarith
      _ ≤ Real.rpow delta (3 * a) / 16 := by linarith
      _ ≤ _ := hmass
  refine ⟨hbudget, ?_⟩
  have hweak : Real.rpow (12 * delta) b ≤ slopeOffsetScale s ^ 2 * Real.rpow delta a := by
    nlinarith
  have hinv := (inv_le_inv₀ (mul_pos (sq_pos_of_pos hk) hp) hpb).2 hweak
  have hneg : Real.rpow delta (-a) = (Real.rpow delta a)⁻¹ := Real.rpow_neg hdelta.le a
  have hneg' : Real.rpow (12 * delta) (-b) = (Real.rpow (12 * delta) b)⁻¹ :=
    Real.rpow_neg (by positivity) b
  rw [hneg, hneg']
  simpa only [mul_inv_rev, mul_comm] using hinv

end Kakeya.Assouad
end
