import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.DirectHalfOffsetTerminalRequestedCWAConstructor
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.DirectHalfOffsetTerminalFinalRestriction
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.DirectHalfOffsetTerminalPublicSlope
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.HorizontalNormalizationTerminalAssembly
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.FinalQuotientLossSchedule

/-!
# Proposition 6.5 before erasing construction witnesses

The common-y source, actual terminal geometry, cleanup, source regularization,
and final joint selection are dependent fields.  In particular the terminal
certificate cannot be attached to a separately selected family or shading.
Lemma 6.7 consumes the terminal projection directly or transports this
literal terminal to its normalized projection preparation.  The common source
also supplies a pre-runtime power bound on the actual terminal slope offset.
-/

noncomputable section
namespace Kakeya.Assouad

open PureWZ2DirectCommonYSourceAssembly
open PureWZ2DirectCommonYSourceAssembly.TerminalGeometry
open PureWZ2DirectCommonYSourceAssembly.TerminalGeometry.PureWZ2ExternalWeightRegularizationData

/-- The completed large-slope construction, retaining its source and every
selection used by the paper-facing output. -/
structure PureWZ2LargeSlopeConstruction
    (logExponent : ℕ) (sigma epsilon outputLoss sourceDelta : ℝ) where
  commonSource : PureWZ2DirectCommonYSourceAssembly
    logExponent sigma epsilon sourceDelta
  terminal : commonSource.TerminalGeometry
  degreeBound : ENNReal
  cleanup : PureWZ2HalfOffsetTerminalDistinctCleanupData
    commonSource terminal degreeBound
  sourceConstant : ENNReal
  scheduleConstant : ENNReal
  normalizationWeight : ENNReal
  levelCount : ℕ
  regularization : PureWZ2HalfOffsetTerminalCleanupSourceRegularizationData
    cleanup sourceConstant scheduleConstant normalizationWeight levelCount
  nearbyLoss : ℝ
  nearbyLoss_eq : nearbyLoss = pureWZ2FinalNearbyLoss outputLoss
  requested : DirectHalfOffsetTerminalRequestedCWAData regularization
    (Kakeya.realRpowENN terminal.targetDelta (-nearbyLoss))
  terminalData : PureWZ2HorizontalTerminalData
    (sigma := sigma) (nearbyLoss := nearbyLoss) (outputLoss := outputLoss)
    (safePublicSlope commonSource terminal)
    requested.finalTarget requested.finalShading

namespace PureWZ2LargeSlopeConstruction

/-- Erase provenance only at the paper-facing boundary. -/
def toLargeSlopeConfiguration
    {logExponent : ℕ} {sigma epsilon outputLoss sourceDelta : ℝ}
    (data : PureWZ2LargeSlopeConstruction
      logExponent sigma epsilon outputLoss sourceDelta) :
    PureWZ2LargeSlopeConfiguration sigma outputLoss data.terminal.targetDelta :=
  data.terminalData.toLargeSlopeConfiguration

end PureWZ2LargeSlopeConstruction

/-- Both scale ceilings are chosen before the source.  The second one allows
a subsequent consumer to preallocate its own normalization losses without
restarting the large-slope construction. -/
def PureWZ2LargeSlopeRetainedStatement : Prop :=
  ∀ sigma : ℝ, PureWZ2CriticalPackage sigma →
    ∀ outputLoss outputDeltaBound sourceDeltaBound : ℝ,
      0 < outputLoss → 0 < outputDeltaBound → 0 < sourceDeltaBound →
        ∃ logExponent : ℕ, ∃ sourceDelta : ℝ,
          0 < sourceDelta ∧ sourceDelta ≤ sourceDeltaBound ∧
          ∃ data : PureWZ2LargeSlopeConstruction logExponent sigma
            (pureWZ2FinalEpsilon outputLoss) outputLoss sourceDelta,
            data.terminal.targetDelta ≤ outputDeltaBound

/-- The strengthened statement implies the unchanged Proposition 6.5 ABI. -/
theorem PureWZ2LargeSlopeRetainedStatement.toLargeSlopeFromCritical
    (retained : PureWZ2LargeSlopeRetainedStatement) :
    PureWZ2LargeSlopeFromCriticalStatement := by
  intro sigma critical outputLoss delta₀ hloss hdelta₀
  rcases retained sigma critical outputLoss delta₀ 1 hloss hdelta₀
      (by norm_num) with
    ⟨_, _, _, _, data, htarget⟩
  exact ⟨data.terminal.targetDelta, data.terminalData.delta_pos, htarget,
    ⟨data.toLargeSlopeConfiguration⟩⟩

end Kakeya.Assouad
end
