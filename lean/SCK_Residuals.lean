import SCJ_AccountProjection
import SCG_AcceptedPair
import SCH_AccountDecoded
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCK_Residuals
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open SCE_Experiment S2W_NativeConsolidation MultiproofConeCanonical

/-- A target, not a theorem or new deployment hypothesis. The first reply
binds saved/post/final to THIS world's run before selecting its second entry. -/
def R1 {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program) (a : Adversary A) : Prop :=
  ∀ H : Bytes → State,
    accepted (eval H (account c hashv copy allocator id a)).2 = true →
    ∃ saved post final f s,
      (eval H (SCE_Execution.firstCode c hashv copy allocator id (eval H a.first).2)).2 =
        ok (.Ok (saved,post,final)) ∧
      SourceCuts (SCH_IdealSdk.dictionary c hashv H) (eval H a.first).2.entry.first
        ((eval H (a.second (eval H a.first).2 saved post final)).2.entry.second secondSizes)
        saved f s ∧
      bytesOf s.checkpoint.val = bytesOf saved.val

/-- The exact event direction needed by the clean branch. Acceptance guarding
is sufficient; unconditional all-log identity is stronger and unnecessary. -/
def R2 {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)
    (a : Adversary A) (Q0 Q1 : Nat)
    (project : GExq_AccountExperiment.Outcome A → OraclePortCompactDraft.Parsed × (Fin 22 → Fin 262144))
    (select : GExq_AccountExperiment.Outcome A → R9PoolRuntimeBinding.Inputs × R9PoolRuntimeBinding.Inputs)
    (sourceSelect : F3X_Projection.Output → R9PoolRuntimeBinding.Inputs × R9PoolRuntimeBinding.Inputs) : Prop :=
  ∀ H : Bytes → State,
    accepted (eval H (account c hashv copy allocator id a)).2 = true →
    BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (Q0+Q1+2965)
      (eval H (Hiq_RecordedJoint.program (F3X_Account.program c hashv (submission a))
        F3X_Projection.project sourceSelect)) →
    BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (Q0+Q1+2965)
      (eval H (Hiq_RecordedJoint.program (account c hashv copy allocator id a) project select))

#print R1
#print R2
end AspisR1.SCK_Residuals
end
