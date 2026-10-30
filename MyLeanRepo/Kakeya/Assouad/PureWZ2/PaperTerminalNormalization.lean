import MyLeanRepo.Kakeya.Assouad.PureWZ2.SlopeOffsetScalarBudget
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Node7AnalyticCleanup
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope
import MyLeanRepo.Kakeya.Assouad.PureWZ2.CommonHeightNormalizedTerminal

/-!
# Normalizing the actual Proposition-6.5 terminal

The output retains the injective source-index map, exact supporting-line
image, subshading containment in the affine image of the chosen source slab,
and the centered source slope.  Every cutoff precedes the paper terminal.
-/

noncomputable section
open MeasureTheory Set
namespace Kakeya.Assouad

/-- Provenance from the supplied paper family all the way through analytic cleanup. -/
structure PureWZ2PaperTerminalProjectionRefinement
    {delta : ℝ} (F : Kakeya.Streamlined.TubeFamily delta)
    (Y : WZ1PaperTubeShading F) (f : SlopeFunction) (sigma loss : ℝ) where
  configuration : PureWZ2NormalizedProjectionData sigma loss (12 * delta)
  center : ℝ
  center_mem : |center| ≤ 1
  source_mass_fraction : Y.mass ≤
    12 * pureWZ2PaperMassInSlab Y (center - 1 / 8) (center + 1 / 8)
  sourceIndex : Fin configuration.family.card → Fin F.card
  sourceIndex_injective : Function.Injective sourceIndex
  tube_eq_model : ∀ i, configuration.family.tube i =
    slopeOffsetModelTube (slopeOffsetParams (f 0) (tubeParams (sourceIndex i))) center (12 * delta)
  axis_image : ∀ i,
    slopeOffsetLinear (f 0) '' tubeAxisLine (F.tube (sourceIndex i)) =
      tubeAxisLine (configuration.family.tube i)
  shading_subset_image : ∀ i, configuration.shading.carrier i ⊆
    slopeOffsetLinear (f 0) ''
      (Y.carrier (sourceIndex i) ∩ horizontalSlab (center - 1 / 8) (center + 1 / 8))
  slope_eq : configuration.analysisSlope = f.centered

/-- Cleanup retains the very unit segments centered in the original retubing. -/
theorem PureWZ2PaperTerminalProjectionRefinement.common_height
    {delta sigma loss : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : WZ1PaperTubeShading F} {f : SlopeFunction}
    (data : PureWZ2PaperTerminalProjectionRefinement F Y f sigma loss) :
    HasCommonHeightTubeModel data.configuration.family := by
  refine ⟨data.center, data.center_mem, ?_⟩
  intro i
  have hparams : tubeParams i = slopeOffsetParams (f 0) (tubeParams (data.sourceIndex i)) := by
    change tubeParamsOfTube (data.configuration.family.tube i) = _
    rw [data.tube_eq_model, slopeOffsetModelTube_params]
  rw [hparams]
  exact data.tube_eq_model i

/-- The final projection is controlled by the actual upstream projection. -/
theorem PureWZ2PaperTerminalProjectionRefinement.projection_volume_le
    {delta sigma loss : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : WZ1PaperTubeShading F} {f : SlopeFunction}
    (data : PureWZ2PaperTerminalProjectionRefinement F Y f sigma loss) :
    volume (twistedUnion data.configuration.shading data.configuration.analysisSlope) ≤
      ENNReal.ofReal (slopeOffsetScale (f 0)) *
        volume (twistedProjection f '' Y.union) := by
  rw [data.slope_eq, twistedUnion, ← slopeOffset_twisted_volume]
  apply measure_mono
  apply Set.image_mono
  rintro p ⟨i, hp⟩
  obtain ⟨q, hq, rfl⟩ := data.shading_subset_image i hp
  exact ⟨q, ⟨data.sourceIndex i, hq.1⟩, rfl⟩

/-- The numerical preparation for the actual paper terminal.  `run` has no
free choice of upstream family, shading or slope after receiving `source`. -/
structure PureWZ2PaperTerminalNormalizationCutoffData (sigma loss : ℝ) where
  delta₀ : ℝ
  delta₀_pos : 0 < delta₀
  radius_small : 12 * delta₀ ≤ 1 / 10000
  run : ∀ {delta : ℝ}
    (source : PureWZ2LargeSlopeConfiguration sigma (loss / 10000) delta),
    delta ≤ delta₀ →
    1 + |source.slope 0| ≤ Real.rpow delta (-(loss / 10000)) →
    Nonempty (PureWZ2PaperTerminalProjectionRefinement
      source.family source.shading source.slope sigma loss)

theorem pure_wz2_paper_terminal_normalization_cutoff
    (sigma loss : ℝ) (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hloss : 0 < loss) (hlossSigma : loss < sigma) :
    Nonempty (PureWZ2PaperTerminalNormalizationCutoffData sigma loss) := by
  obtain ⟨cleanup⟩ := pure_wz2_node7_analytic_cleanup_cutoff
    sigma loss hsigma hsigmaOne hloss hlossSigma
  obtain ⟨scalarCutoff, hscalarPos, hscalarOne, hscalar⟩ :=
    exists_slopeOffset_normalization_budget (loss / 10000) (loss / 100)
      (by positivity) (by linarith) (by linarith)
  let delta₀ := min (cleanup.r₀ / 12) scalarCutoff
  refine ⟨{
    delta₀ := delta₀
    delta₀_pos := lt_min (by positivity [cleanup.r₀_pos]) hscalarPos
    radius_small := ?_
    run := ?_ }⟩
  · have h := min_le_left (cleanup.r₀ / 12) scalarCutoff
    dsimp only [delta₀]
    linarith [cleanup.r₀_le_small]
  · intro delta source hcutoff hslope
    have hdelta := source.extremal.delta_pos
    have hdeltaOne := source.extremal.delta_le_one
    have hfinal : 12 * delta ≤ cleanup.r₀ := by
      have h := hcutoff.trans (min_le_left _ _)
      linarith
    have hfinalPos : 0 < 12 * delta := by positivity
    have hfinalOne : 12 * delta ≤ 1 := hfinal.trans
      (cleanup.r₀_le_small.trans (by norm_num))
    have hbudget := hscalar hdelta (hcutoff.trans (min_le_right _ _)) (source.slope 0) hslope
    obtain ⟨m, hm, hmass⟩ := exists_slopeOffset_mass_slab source.shading
    let F := slopeOffsetRetubedFamily source.family (source.slope 0) m
    let Y := slopeOffsetSlabShading source.shading hdelta.le source.line_class (source.slope 0) m
    have hline : WZ1PaperIsLineClass F :=
      slopeOffsetRetubedFamily_lineClass source.family source.line_class _ _
    have hcwa : WZ2PaperConvexWolffBound F
        (Kakeya.realRpowENN (12 * delta) (-(loss / 100))) := by
      have hconstant : ENNReal.ofReal ((slopeOffsetScale (source.slope 0) ^ 2)⁻¹) *
          Kakeya.realRpowENN delta (-(loss / 10000)) ≤
          Kakeya.realRpowENN (12 * delta) (-(loss / 100)) := by
        simpa only [Kakeya.realRpowENN, ENNReal.ofReal_mul (by positivity :
          0 ≤ (slopeOffsetScale (source.slope 0) ^ 2)⁻¹)] using ENNReal.ofReal_mono hbudget.2
      intro K hK
      exact (slopeOffsetRetubedFamily_cwa hdelta.le source.line_class
        (source.slope 0) m source.top_level_cwa K hK).trans (by gcongr)
    have hdense : Y.IsLambdaDense (Kakeya.realRpowENN (12 * delta) (loss / 100)) := by
      apply slopeOffsetSlabShading_dense source.shading hdelta hfinalOne source.line_class
        (source.slope 0) m hmass source.extremal.dense
      have h := ENNReal.ofReal_mono hbudget.1
      simpa only [Kakeya.realRpowENN, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 20736),
        ENNReal.ofReal_mul (sq_nonneg _), show ENNReal.ofReal (20736 : ℝ) = 20736 by norm_num] using h
    have hupper : volume (twistedUnion Y source.slope.centered) ≤
        Kakeya.realRpowENN (12 * delta) (sigma - loss) := by
      calc
        _ ≤ ENNReal.ofReal (slopeOffsetScale (source.slope 0)) *
            volume (twistedProjection source.slope '' source.shading.union) :=
          slopeOffsetSlabShading_projection source.shading hdelta.le source.line_class _ m
        _ ≤ 1 * Kakeya.realRpowENN delta (sigma - loss / 10000) := by
          gcongr
          · exact (ENNReal.ofReal_le_one).mpr ((slopeOffsetScale_le_quarter _).trans (by norm_num))
          · exact source.projection_upper
        _ = Kakeya.realRpowENN delta (sigma - loss / 10000) := one_mul _
        _ ≤ Kakeya.realRpowENN delta (sigma - loss) := by
          apply ENNReal.ofReal_mono
          exact Real.rpow_le_rpow_of_exponent_ge hdelta hdeltaOne (by linarith)
        _ ≤ Kakeya.realRpowENN (12 * delta) (sigma - loss) := by
          apply ENNReal.ofReal_mono
          exact Real.rpow_le_rpow hdelta.le (by linarith) (by linarith)
    obtain ⟨refined⟩ := cleanup.runWithCWA F Y hloss hfinalPos hfinal
      source.extremal.nonempty
      (slopeOffsetRetubedFamily_base_bound source.family source.line_class _ _ hm)
      hline.vertical (slopeOffsetSlabShading_window source.shading hdelta.le source.line_class _ _)
      hline hcwa hdense source.slope.centered (by simp)
      (SlopeFunction.centered_isNonsingular source.slope_nonsingular) hupper
    have hslopeCentered : source.slope.centered.centered = source.slope.centered := by
      cases source.slope with
      | mk toFun contDiff =>
        simp only [SlopeFunction.centered]
        congr
        funext z
        simp
    exact ⟨{
      configuration := refined.configuration
      center := m
      center_mem := hm
      source_mass_fraction := hmass
      sourceIndex := refined.sourceIndex
      sourceIndex_injective := refined.sourceIndex_injective
      tube_eq_model := refined.tube_eq_source
      axis_image := by
        intro i
        rw [refined.tube_eq_source]
        exact slopeOffsetLinear_axis_image _ (source.line_class (refined.sourceIndex i)) _ _ _
      shading_subset_image := refined.shading_subset_source
      slope_eq := refined.slope_eq.trans hslopeCentered }⟩

end Kakeya.Assouad
end
