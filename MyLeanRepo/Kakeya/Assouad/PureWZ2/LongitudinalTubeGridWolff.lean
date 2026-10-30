import MyLeanRepo.Kakeya.Assouad.PureWZ2.LongitudinalTubeGridGeometry

/-! Ordinary capsule Tube Wolff counting for the longitudinal grid.
Both line parameters and the actual segment center enter the count. -/

noncomputable section
open MeasureTheory Set
namespace Kakeya.Assouad

theorem fin_grid_interval_count_mul_add {N : ℕ} {mesh r : ℝ}
    (hmesh : 0 < mesh) (hr : 0 ≤ r) (reference : Fin N) :
    mesh * ((Finset.univ.filter fun i : Fin N =>
      |mesh * (i : ℝ) - mesh * (reference : ℝ)| ≤ r).card : ℝ) ≤ 2 * r + mesh := by
  classical
  let indices := Finset.univ.filter fun i : Fin N =>
    |mesh * (i : ℝ) - mesh * (reference : ℝ)| ≤ r
  have hnonempty : indices.Nonempty :=
    ⟨reference, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp; exact hr⟩⟩
  let low := indices.min' hnonempty
  let high := indices.max' hnonempty
  have hlow := indices.min'_mem hnonempty
  have hhigh := indices.max'_mem hnonempty
  have hle : low ≤ high := indices.min'_le _ hhigh
  have hsubset : indices ⊆ Finset.Icc low high := by
    intro i hi
    exact Finset.mem_Icc.mpr ⟨indices.min'_le _ hi, indices.le_max' _ hi⟩
  have hcard : indices.card ≤ high.val + 1 - low.val := by
    simpa only [Fin.card_Icc] using Finset.card_le_card hsubset
  have hcardReal : (indices.card : ℝ) ≤ (high : ℝ) + 1 - (low : ℝ) := by
    have hle' : low.val ≤ high.val := hle
    have hnat : low.val ≤ high.val + 1 := hle'.trans (Nat.le_succ _)
    have hreal : (indices.card : ℝ) ≤ ((high.val + 1 - low.val : ℕ) : ℝ) := by exact_mod_cast hcard
    simpa only [Nat.cast_sub hnat, Nat.cast_add, Nat.cast_one] using hreal
  have hl := (Finset.mem_filter.mp hlow).2
  have hh := (Finset.mem_filter.mp hhigh).2
  change mesh * (indices.card : ℝ) ≤ 2 * r + mesh
  nlinarith [abs_le.mp hl, abs_le.mp hh]

theorem longitudinalTubeGrid_center_count {n : ℕ} (hn : 0 < n)
    {r : ℝ} (hr : 0 ≤ r) (reference : Fin n) :
    ((Finset.univ.filter fun i : Fin n =>
      |planarTubeGridMesh n * (i : ℝ) - planarTubeGridMesh n * (reference : ℝ)| ≤ 4*r).card : ℝ) ≤
        1 + 512 * r * (n : ℝ) := by
  have hm := planarTubeGridMesh_pos hn
  have h := fin_grid_interval_count_mul_add hm (by positivity : 0 ≤ 4*r) reference
  have hc : ((Finset.univ.filter fun i : Fin n =>
      |planarTubeGridMesh n * (i : ℝ) - planarTubeGridMesh n * (reference : ℝ)| ≤ 4*r).card : ℝ) ≤
      (2*(4*r) + planarTubeGridMesh n) / planarTubeGridMesh n := by
    apply (le_div_iff₀ hm).2
    simpa only [mul_comm] using h
  calc
    _ ≤ _ := hc
    _ = 1 + 512*r*(n : ℝ) := by
      rw [add_div, div_self hm.ne']
      simp only [planarTubeGridMesh, div_eq_mul_inv, inv_inv]
      ring

theorem longitudinalTubeGrid_fine_count {n N : ℕ} (hn : 0 < n)
    {r : ℝ} (hdr : planarTubeGridScale (n*n) ≤ r) (reference : Fin N) :
    ((Finset.univ.filter fun i : Fin N =>
      |planarTubeGridMesh (n*n) * (i : ℝ) - planarTubeGridMesh (n*n) * (reference : ℝ)| ≤ 320*r).card : ℝ) ≤
        65536 * r * (n : ℝ)^2 := by
  have hm := planarTubeGridMesh_pos (Nat.mul_pos hn hn)
  have hr := (planarTubeGridScale_pos (Nat.mul_pos hn hn)).trans_le hdr
  have hmr : planarTubeGridMesh (n*n) ≤ 320*r := by
    dsimp only [planarTubeGridScale] at hdr
    linarith
  have h := fin_grid_interval_count_mul hm hmr reference
  have hc : ((Finset.univ.filter fun i : Fin N =>
      |planarTubeGridMesh (n*n) * (i : ℝ) - planarTubeGridMesh (n*n) * (reference : ℝ)| ≤ 320*r).card : ℝ) ≤
      (3*(320*r)) / planarTubeGridMesh (n*n) := by
    apply (le_div_iff₀ hm).2
    simpa only [mul_comm] using h
  calc
    _ ≤ _ := hc
    _ = 61440*r*(n : ℝ)^2 := by
      simp only [planarTubeGridMesh, div_eq_mul_inv, inv_inv, Nat.cast_mul]
      ring
    _ ≤ _ := by gcongr; norm_num

theorem longitudinalTubeGrid_tubeWolff {n : ℕ} (hn : 0 < n) :
    TubeWolffBound (longitudinalTubeGrid n) 1152921504606846976 := by
  classical
  intro r hdr hrOne T
  let F := longitudinalTubeGrid n
  let contained := F.toBodyFamily.containedIndices T.carrier
  have hdelta := planarTubeGridScale_pos (Nat.mul_pos hn hn)
  have hr : 0 < r := hdelta.trans_le hdr
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hcardAll : (contained.card : ℝ) ≤ (n : ℝ)^5 := by
    have h := Finset.card_le_card (Finset.subset_univ contained)
    have hsize : (Finset.univ : Finset (Fin F.toBodyFamily.card)).card = n^5 := by
      rw [Finset.card_univ, Fintype.card_fin]
      change (longitudinalTubeGrid n).card = n^5
      exact longitudinalTubeGrid_card n
    rw [hsize] at h
    exact_mod_cast h
  have hreal : (contained.card : ℝ) ≤ 1152921504606846976 * r^2 * (n : ℝ)^5 := by
    by_cases hsmall : r ≤ 1 / 8
    · by_cases hempty : contained.Nonempty
      · obtain ⟨reference, href⟩ := hempty
        let e := (Fintype.equivFin (LongitudinalTubeGridIndex n)).symm
        let k := e reference
        let A := Finset.univ.filter fun i : Fin n =>
          |planarTubeGridMesh n * (i : ℝ) - planarTubeGridMesh n * (k.1.1 : ℝ)| ≤ 4*r
        let B := Finset.univ.filter fun i : Fin (n*n) =>
          |planarTubeGridMesh (n*n) * (i : ℝ) - planarTubeGridMesh (n*n) * (k.1.2 : ℝ)| ≤ 320*r
        let U := Finset.univ.filter fun i : Fin n =>
          |planarTubeGridMesh (n*n) * (i : ℝ) - planarTubeGridMesh (n*n) * (k.2.1 : ℝ)| ≤ 320*r
        let D := Finset.univ.filter fun i : Fin n =>
          |planarTubeGridMesh (n*n) * (i : ℝ) - planarTubeGridMesh (n*n) * (k.2.2 : ℝ)| ≤ 320*r
        have hsubset : contained.image e ⊆ (A.product B).product (U.product D) := by
          intro value hvalue
          obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hvalue
          have hiT := Kakeya.Streamlined.BodyFamily.mem_containedIndices_iff.mp hi
          have hrefT := Kakeya.Streamlined.BodyFamily.mem_containedIndices_iff.mp href
          have hparams := ordinary_capsule_pair_parameter_bounds hdelta.le hr.le hsmall
            (F.tube i) (F.tube reference) T (longitudinalTubeGrid_lineClass hn i).vertical
            (longitudinalTubeGrid_axisPoint_mem_segment hn i)
            (longitudinalTubeGrid_axisPoint_mem_segment hn reference) hiT hrefT
          have hm := ordinary_capsule_pair_center_height hdelta.le hr.le
            (F.tube i) (F.tube reference) T hiT hrefT
          have hu : |((tubeParamsOfTube (F.tube i)).b + (tubeParamsOfTube (F.tube i)).c) -
              ((tubeParamsOfTube (F.tube reference)).b + (tubeParamsOfTube (F.tube reference)).c)| ≤ 320*r := by
            rw [show ((tubeParamsOfTube (F.tube i)).b + (tubeParamsOfTube (F.tube i)).c) -
                ((tubeParamsOfTube (F.tube reference)).b + (tubeParamsOfTube (F.tube reference)).c) =
              ((tubeParamsOfTube (F.tube i)).b - (tubeParamsOfTube (F.tube reference)).b) +
                ((tubeParamsOfTube (F.tube i)).c - (tubeParamsOfTube (F.tube reference)).c) by ring]
            exact (abs_add_le _ _).trans (by linarith [hparams.2.1, hparams.2.2.1])
          simp only [F, longitudinalTubeGrid_center, longitudinalTubeGridCenter] at hm
          simp only [F, longitudinalTubeGrid_params, longitudinalTubeGridParams, sub_add_cancel] at hu
          have hc := hparams.2.2.1.trans (show 160*r ≤ 320*r by linarith)
          have hd := hparams.2.2.2.trans (show 160*r ≤ 320*r by linarith)
          simp only [F, longitudinalTubeGrid_params, longitudinalTubeGridParams] at hc hd
          exact Finset.mem_product.mpr ⟨Finset.mem_product.mpr
            ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm⟩,
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩⟩,
            Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu⟩,
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd⟩⟩⟩
        have hcard : (contained.card : ℝ) ≤
            ((A.card : ℝ) * B.card) * ((U.card : ℝ) * D.card) := by
          have h := Finset.card_le_card hsubset
          rw [Finset.card_image_of_injective _ e.injective] at h
          have hp : ((A.product B).product (U.product D)).card =
              (A.card * B.card) * (U.card * D.card) :=
            (Finset.card_product (A.product B) (U.product D)).trans
              (congrArg₂ (· * ·) (Finset.card_product A B) (Finset.card_product U D))
          rw [hp] at h
          exact_mod_cast h
        have hA : (A.card : ℝ) ≤ 1 + 512*r*(n : ℝ) := longitudinalTubeGrid_center_count hn hr.le _
        have hB : (B.card : ℝ) ≤ 65536*r*(n : ℝ)^2 := longitudinalTubeGrid_fine_count hn hdr _
        have hU : (U.card : ℝ) ≤ 65536*r*(n : ℝ)^2 := longitudinalTubeGrid_fine_count hn hdr _
        have hD : (D.card : ℝ) ≤ 65536*r*(n : ℝ)^2 := longitudinalTubeGrid_fine_count hn hdr _
        by_cases hscale : r * (n : ℝ) ≤ 1
        · have hA' : (A.card : ℝ) ≤ 513 := by linarith
          calc
            _ ≤ _ := hcard
            _ ≤ (513 * (65536*r*(n : ℝ)^2)) *
                ((65536*r*(n : ℝ)^2) * (65536*r*(n : ℝ)^2)) := by gcongr
            _ = (513 * 65536^3) * (r*(n : ℝ)) * (r^2*(n : ℝ)^5) := by ring
            _ ≤ (513 * 65536^3) * 1 * (r^2*(n : ℝ)^5) := by gcongr
            _ = (513 * 65536^3) * (r^2*(n : ℝ)^5) := by ring
            _ ≤ 1152921504606846976 * (r^2*(n : ℝ)^5) :=
              mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
            _ = _ := by ring
        · have hA' : (A.card : ℝ) ≤ 513*r*(n : ℝ) := by linarith
          have hUn : (U.card : ℝ) ≤ n := by
            have h := Finset.card_le_card (Finset.subset_univ U)
            simpa using (show (U.card : ℝ) ≤ (Finset.univ : Finset (Fin n)).card by exact_mod_cast h)
          have hDn : (D.card : ℝ) ≤ n := by
            have h := Finset.card_le_card (Finset.subset_univ D)
            simpa using (show (D.card : ℝ) ≤ (Finset.univ : Finset (Fin n)).card by exact_mod_cast h)
          calc
            _ ≤ _ := hcard
            _ ≤ ((513*r*(n : ℝ)) * (65536*r*(n : ℝ)^2)) * ((n : ℝ)*n) := by gcongr
            _ = (513*65536) * (r^2*(n : ℝ)^5) := by ring
            _ ≤ 1152921504606846976 * (r^2*(n : ℝ)^5) :=
              mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
            _ = _ := by ring
      · rw [Finset.not_nonempty_iff_eq_empty.mp hempty, Finset.card_empty, Nat.cast_zero]
        positivity
    · calc
        _ ≤ (n : ℝ)^5 := hcardAll
        _ ≤ 1152921504606846976 * r^2 * (n : ℝ)^5 := by
          have hfactor : (1 : ℝ) ≤ 1152921504606846976 * r^2 := by nlinarith
          simpa using mul_le_mul_of_nonneg_right hfactor (by positivity : 0 ≤ (n : ℝ)^5)
  have h := ENNReal.ofReal_mono hreal
  have hrpow : Real.rpow r 2 = r^2 := Real.rpow_two r
  change (contained.card : ENNReal) ≤ _
  have hcardENN : F.enncard = (n : ENNReal)^5 := by
    simp [Kakeya.Streamlined.TubeFamily.enncard, F, longitudinalTubeGrid_card]
  rw [hcardENN]
  simpa [Kakeya.realRpowENN, hrpow, ENNReal.ofReal_mul, ENNReal.ofReal_pow,
    hr.le, hnR.le] using h

end Kakeya.Assouad
end
