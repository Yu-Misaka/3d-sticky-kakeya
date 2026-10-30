import MyLeanRepo.Kakeya.Assouad.PureWZ2.SlopeOffsetRetubing
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Proposition64ShortSlab
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperCarrierVolumeLower
import MyLeanRepo.Kakeya.Assouad.TubeVolumeLowerBound
import MyLeanRepo.Kakeya.Assouad.TubeVolumeScaling

/-!
# Mass and CWA transport of the supplied paper terminal

All retubed members have the original indices.  The shading is the exact
image of a restriction of the supplied shading.  A fixed-width slab retains
at least one twelfth of indexed mass.  The sole spatial Jacobian is k².
-/

noncomputable section
open MeasureTheory Set
namespace Kakeya.Assouad

def slopeOffsetRetubedFamily {delta : ℝ}
    (F : Kakeya.Streamlined.TubeFamily delta) (s m : ℝ) :
    Kakeya.Streamlined.TubeFamily (12 * delta) where
  card := F.card
  tube i := slopeOffsetModelTube (slopeOffsetParams s (tubeParamsOfTube (F.tube i)))
    m (12 * delta)

theorem slopeOffsetRetubedFamily_lineClass {delta : ℝ}
    (F : Kakeya.Streamlined.TubeFamily delta) (hline : WZ1PaperIsLineClass F)
    (s m : ℝ) : WZ1PaperIsLineClass (slopeOffsetRetubedFamily F s m) := by
  intro i
  have hb := slopeOffsetParams_bounds_of_lineClass (F.tube i) (hline i) s
  exact slopeOffsetModelTube_lineClass _ m _
    (hb.1.trans (by norm_num)) (hb.2.1.trans (by norm_num)) hb.2.2.1 hb.2.2.2

theorem slopeOffsetRetubedFamily_base_bound {delta : ℝ}
    (F : Kakeya.Streamlined.TubeFamily delta) (hline : WZ1PaperIsLineClass F)
    (s m : ℝ) (hm : |m| ≤ 1) : HasBoundedBase (slopeOffsetRetubedFamily F s m) 4 := by
  intro i
  have hb := slopeOffsetParams_bounds_of_lineClass (F.tube i) (hline i) s
  exact slopeOffsetModelTube_base_bound _ m _ hb.1 hb.2.1 hb.2.2.1 hb.2.2.2 hm

def slopeOffsetSlabShading {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta} (Y : WZ1PaperTubeShading F)
    (hdelta : 0 ≤ delta) (hline : WZ1PaperIsLineClass F) (s m : ℝ) :
    Kakeya.Streamlined.TubeShading (slopeOffsetRetubedFamily F s m) where
  carrier i := slopeOffsetLinear s ''
    (Y.carrier i ∩ horizontalSlab (m - 1 / 8) (m + 1 / 8))
  measurable_carrier i := by
    let e := (slopeOffsetLinear s).toAffineEquiv.toHomeomorphOfFiniteDimensional.toMeasurableEquiv
    exact e.measurableSet_image.mpr
      ((Y.measurable_carrier i).inter (measurableSet_horizontalSlab _ _))
  subset_body i := by
    exact Set.Subset.trans
      (Set.image_mono (Set.inter_subset_inter_left _ (Y.subset_body i)))
      (slopeOffsetLinear_slabCarrier_subset hdelta (F.tube i) (hline i) s m)

theorem slopeOffsetSlabShading_union {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta} (Y : WZ1PaperTubeShading F)
    (hdelta : 0 ≤ delta) (hline : WZ1PaperIsLineClass F) (s m : ℝ) :
    (slopeOffsetSlabShading Y hdelta hline s m).union =
      slopeOffsetLinear s '' (Y.union ∩ horizontalSlab (m - 1 / 8) (m + 1 / 8)) := by
  ext p
  constructor
  · rintro ⟨i, q, ⟨hq, hslab⟩, rfl⟩
    exact ⟨q, ⟨⟨i, hq⟩, hslab⟩, rfl⟩
  · rintro ⟨q, ⟨⟨i, hq⟩, hslab⟩, rfl⟩
    exact ⟨i, q, ⟨hq, hslab⟩, rfl⟩

theorem slopeOffsetSlabShading_window {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta} (Y : WZ1PaperTubeShading F)
    (hdelta : 0 ≤ delta) (hline : WZ1PaperIsLineClass F) (s m : ℝ) :
    IsInSlopeWindow (slopeOffsetSlabShading Y hdelta hline s m) := by
  rintro p ⟨i, q, hq, rfl⟩
  have hb := (Y.subset_body i hq.1).2.2.2
  simpa [Kakeya.Streamlined.axisBox, horizontalSlab, abs_le] using hb

theorem slopeOffsetSlabShading_mass {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta} (Y : WZ1PaperTubeShading F)
    (hdelta : 0 ≤ delta) (hline : WZ1PaperIsLineClass F) (s m : ℝ) :
    (slopeOffsetSlabShading Y hdelta hline s m).mass =
      ENNReal.ofReal (slopeOffsetScale s ^ 2) *
        pureWZ2PaperMassInSlab Y (m - 1 / 8) (m + 1 / 8) := by
  simp only [Kakeya.Streamlined.Shading.mass, slopeOffsetSlabShading,
    slopeOffsetLinear_volume_image, pureWZ2PaperMassInSlab, Finset.mul_sum]
  rfl

theorem slopeOffsetSlabShading_projection {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta} (Y : WZ1PaperTubeShading F)
    (hdelta : 0 ≤ delta) (hline : WZ1PaperIsLineClass F) (f : SlopeFunction) (m : ℝ) :
    volume (twistedUnion (slopeOffsetSlabShading Y hdelta hline (f 0) m) f.centered) ≤
      ENNReal.ofReal (slopeOffsetScale (f 0)) *
        volume (twistedProjection f '' Y.union) := by
  rw [twistedUnion, slopeOffsetSlabShading_union, slopeOffset_twisted_volume]
  apply mul_le_mul_right
  exact measure_mono (Set.image_mono Set.inter_subset_left)

theorem slopeOffsetRetubedFamily_cwa {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (hdelta : 0 ≤ delta) (hline : WZ1PaperIsLineClass F) (s m : ℝ)
    {C : ENNReal} (hC : WZ2PaperConvexWolffBound F C) :
    WZ2PaperConvexWolffBound (slopeOffsetRetubedFamily F s m)
      (ENNReal.ofReal ((slopeOffsetScale s ^ 2)⁻¹) * C) := by
  apply wz2PaperBodyConvexWolffBound_of_affineTransport
    (source := wz1PaperBodyFamily F)
    (target := wz1PaperBodyFamily (slopeOffsetRetubedFamily F s m))
    (slopeOffsetLinear s).toAffineEquiv (Equiv.refl _)
  · intro i
    exact slopeOffsetLinear_paperCarrier_subset hdelta (F.tube i) (hline i) s m
  · intro E
    exact (slopeOffsetLinear_volume_inverse s E).le
  · exact hC

/-- The source-mass pigeonhole uses the actual indexed shading. -/
theorem exists_slopeOffset_mass_slab {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta} (Y : WZ1PaperTubeShading F) :
    ∃ m : ℝ, |m| ≤ 1 ∧ Y.mass ≤
      12 * pureWZ2PaperMassInSlab Y (m - 1 / 8) (m + 1 / 8) := by
  obtain ⟨a, b, ha, hab, hb, hwidth, hmass⟩ := pureWZ2_exists_exact_mass_slab
    Y (L := 1 / 4) (by norm_num) (by norm_num) (by
      intro i p hp
      have h := (Y.subset_body i hp).2.2.2
      simpa [Kakeya.Streamlined.axisBox, horizontalSlab, abs_le] using h)
  refine ⟨(a + b) / 2, abs_le.mpr ⟨by linarith, by linarith⟩, ?_⟩
  have ha' : (a + b) / 2 - 1 / 8 = a := by linarith
  have hb' : (a + b) / 2 + 1 / 8 = b := by linarith
  rw [ha', hb']
  calc
    _ = (4 : ENNReal) * (ENNReal.ofReal (1 / 4) * Y.mass) := by
      norm_num [ENNReal.ofReal_div_of_pos, ← mul_assoc, ENNReal.mul_inv_cancel]
    _ ≤ 4 * (3 * pureWZ2PaperMassInSlab Y a b) := mul_le_mul_right hmass 4
    _ = _ := by ring

theorem slopeOffsetRetubedFamily_mass_le {delta : ℝ}
    (F : Kakeya.Streamlined.TubeFamily delta) (s m : ℝ)
    (hdelta : 0 < delta) (hsmall : 12 * delta ≤ 1) :
    (slopeOffsetRetubedFamily F s m).toBodyFamily.mass ≤
      1728 * (F.enncard * ENNReal.ofReal (delta ^ 2)) := by
  have hvol : Kakeya.deltaTubeVolume (12 * delta) ≤ ENNReal.ofReal (1728 * delta ^ 2) := by
    apply (canonical_volume_upper_tight (by positivity) hsmall).trans
    apply ENNReal.ofReal_mono
    nlinarith [sq_nonneg delta]
  rw [tubeFamily_mass_eq_nominal]
  change F.enncard * Kakeya.deltaTubeVolume (12 * delta) ≤ _
  calc
    _ ≤ F.enncard * ENNReal.ofReal (1728 * delta ^ 2) := mul_le_mul_right hvol _
    _ = _ := by rw [ENNReal.ofReal_mul (by norm_num)]; norm_num; ring

/-- A scalar receipt suffices for density, after the exact image and slab
mass have been computed.  No assumption about the final shading is added. -/
theorem slopeOffsetSlabShading_dense {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta} (Y : WZ1PaperTubeShading F)
    (hdelta : 0 < delta) (hsmall : 12 * delta ≤ 1)
    (hline : WZ1PaperIsLineClass F) (s m : ℝ)
    (hmass : Y.mass ≤ 12 * pureWZ2PaperMassInSlab Y (m - 1 / 8) (m + 1 / 8))
    {lambda targetLambda : ENNReal} (hdense : Y.IsLambdaDense lambda)
    (hbudget : 20736 * targetLambda ≤ ENNReal.ofReal (slopeOffsetScale s ^ 2) * lambda) :
    (slopeOffsetSlabShading Y hdelta.le hline s m).IsLambdaDense targetLambda := by
  have hsource : F.enncard * ENNReal.ofReal (delta ^ 2) ≤ (wz1PaperBodyFamily F).mass := by
    calc
      _ = ∑ _i : Fin F.card, ENNReal.ofReal (delta ^ 2) := by
        simp [Finset.sum_const, Kakeya.Streamlined.TubeFamily.enncard]
      _ ≤ ∑ i : Fin F.card, volume (wz1PaperTubeCarrier (F.tube i)) := by
        apply Finset.sum_le_sum
        intro i _
        exact (canonical_volume_lower hdelta).trans
          (wz2PaperTubeCarrier_volume_lower hdelta (by linarith) (F.tube i) (hline i))
      _ = _ := rfl
  have hraw : ENNReal.ofReal (slopeOffsetScale s ^ 2) * lambda *
      (F.enncard * ENNReal.ofReal (delta ^ 2)) ≤
        12 * (slopeOffsetSlabShading Y hdelta.le hline s m).mass := by
    calc
      _ ≤ ENNReal.ofReal (slopeOffsetScale s ^ 2) * Y.mass := by
        rw [mul_assoc]
        exact mul_le_mul_right ((mul_le_mul_right hsource lambda).trans hdense) _
      _ ≤ ENNReal.ofReal (slopeOffsetScale s ^ 2) *
          (12 * pureWZ2PaperMassInSlab Y (m - 1 / 8) (m + 1 / 8)) :=
        mul_le_mul_right hmass _
      _ = _ := by rw [slopeOffsetSlabShading_mass]; ring
  have htarget : 12 * (targetLambda *
      (slopeOffsetRetubedFamily F s m).toBodyFamily.mass) ≤
        12 * (slopeOffsetSlabShading Y hdelta.le hline s m).mass := by
    calc
      _ ≤ 12 * (targetLambda * (1728 * (F.enncard * ENNReal.ofReal (delta ^ 2)))) := by
        gcongr
        exact slopeOffsetRetubedFamily_mass_le F s m hdelta hsmall
      _ = (20736 * targetLambda) * (F.enncard * ENNReal.ofReal (delta ^ 2)) := by ring
      _ ≤ _ := (mul_le_mul_left hbudget _).trans hraw
  exact (ENNReal.mul_le_mul_iff_right (by norm_num : (12 : ENNReal) ≠ 0)
    (by norm_num : (12 : ENNReal) ≠ ⊤)).mp htarget

end Kakeya.Assouad
end
