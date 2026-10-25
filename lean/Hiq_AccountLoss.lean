import Hiq_CommonEvent
import Hiq_ExactMargin
import Hiq_BindingFailure
import Hiq_AccountEvent
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hiq_AccountLoss
open Aeneas Aeneas.Std Result GExq_AccountExperiment S2Trust S2W_D189Entry S2W_D189Wrappers
open FS FS2 FS2.Duplex DrvC_Installation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.CausalFirstHitUnionBound
variable {A F C : Type} (c : Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)
    (adversary : Program Bytes State (FirstInputs A))
    (chooseSecond : FirstInputs A → alloc.vec.Vec U8 → Heap (Nat → Record) → A → Program Bytes State (SecondInputs A))

theorem one_loss (Q0 Q1 : Nat)
    (prefixBound : ∀ H, (eval H adversary).1.length ≤ Q0)
    (choiceBound : ∀ input saved post final H, (eval H (chooseSecond input saved post final)).1.length ≤ Q1)
    (project : GExq_AccountExperiment.Outcome A → OraclePortCompactDraft.Parsed × (Fin 22 → Fin 262144)) :
    lazyMean (Hiq_DrvRecorded.program c hashv copy allocator id adversary chooseSecond project) emptyTable
      (fun v => indicator (BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (Q0+Q1+2965) v)) ≤
      Hiq_Numeric.accountLoss (Q0+Q1) := by
  have bound := Hiq_RecordedBudget.collision (Hiq_DrvExperiment.source c hashv copy allocator id adversary chooseSecond)
    project (Hiq_ByteSelection.select (sdk c) id) (Q0+Q1+1921)
    (Hiq_DrvExperiment.source_budget c hashv copy allocator id adversary chooseSecond Q0 Q1 prefixBound choiceBound)
  rw [Hiq_Numeric.account_replay (Q0+Q1)] at bound
  simpa only [Hiq_DrvRecorded.program,show Q0+Q1+1921+1044 = Q0+Q1+2965 by omega] using bound

#print axioms one_loss
end AspisR1.Hiq_AccountLoss
end
