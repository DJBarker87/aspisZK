import Hir_IdealJoint
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hir_ExactMargin
open Aeneas Aeneas.Std Result Hist_Store Hist_RuntimeEntry
open FS FS2 FS2.Duplex AspisV8PairedCommitment
open S2Trust S2W_D189Entry S2W_D189Wrappers Hir_Call Hir_Schedule Hir_LifetimeExperiment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.CausalFirstHitUnionBound

/-- Exact frozen-envelope arithmetic with the ACTUAL selected account event.
This is not a probability refinement for deployedFailure or a release claim. -/
theorem event_margin {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (native1 : S2W_ExtractionBoundary.First)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)
    (initial : Store) (schedule : Schedule A (Call A))
    (scheduledBound : ∀ H, (eval H (Hir_Schedule.program native1 copy allocator id c hashv initial schedule)).1.length ≤ 1018)
    (project : Execution A → OraclePortCompactDraft.Parsed × (Fin 22 → Fin 262144)) :
    (1/(2:Rat)^100 - Hiq_Numeric.total 0 =
      1/(2:Rat)^108 - 6*((1161:Rat)^2+2961^2)/(2:Rat)^256 -
        1/(2:Rat)^126 - 1/(2:Rat)^454 - 142224/(2:Rat)^256) ∧
    34*PerAttemptEnvelope.B +
      (6*(1161:Rat)^2/(2:Rat)^256 +
        lazyMean (Hir_SelectedJoint.program c hashv native1 copy allocator id initial schedule project) emptyTable
          (fun v => indicator (BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv 2965 v))) +
      1/(2:Rat)^126 + 1/(2:Rat)^454 < 1/(2:Rat)^100 - 1/(2:Rat)^109 := by
  refine ⟨Hiq_ExactMargin.exact_margin,?_⟩
  have bound := Hir_SelectedJoint.one_loss c hashv native1 copy allocator id initial schedule 0 0 scheduledBound project
  have totalBound : 34*PerAttemptEnvelope.B +
      (6*(1161:Rat)^2/(2:Rat)^256 +
        lazyMean (Hir_SelectedJoint.program c hashv native1 copy allocator id initial schedule project) emptyTable
          (fun v => indicator (BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv 2965 v))) +
      1/(2:Rat)^126 + 1/(2:Rat)^454 ≤ Hiq_Numeric.total 0 := by
    unfold Hiq_Numeric.total Hiq_Numeric.accountLoss
    gcongr <;> norm_num
  have margin := Hiq_ExactMargin.positive_margin
  linarith

#print axioms event_margin
end AspisR1.Hir_ExactMargin
end
