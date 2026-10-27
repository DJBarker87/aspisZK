import RPz7_RawJ_AccountBudget
import RPz7_SdkC_Replay
set_option autoImplicit false
noncomputable section
namespace AspisR1.RawJ_CollisionBudget
open Aeneas Aeneas.Std Result GExq_AccountExperiment S2Trust S2W_D189Entry S2W_D189Wrappers
open FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.CausalFirstHitUnionBound
variable {A F C : Type} (adapter : AdapterRw.Ops) (current : AspisR1CurrentCaller.Ops)
    (stage : VTop_Stages.Ops) (finish : AspisR1Stage2.Stage2Finish.FinishOps F) (reserved : Bool)
    (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)
    (adversary : Program Bytes State (FirstInputs A))
    (chooseSecond : FirstInputs A → alloc.vec.Vec U8 → Heap (Nat → Record) → A → Program Bytes State (SecondInputs A))
    (Q0 Q1 : Nat)
    (prefixBound : ∀ H, (eval H adversary).1.length ≤ Q0)
    (choiceBound : ∀ input saved post final H, (eval H (chooseSecond input saved post final)).1.length ≤ Q1)

include prefixBound choiceBound

theorem first_reads (H : Bytes → State) :
    firstReads emptyTable
      (eval H (program adapter current stage finish reserved query geo B std hashv copy allocator id adversary chooseSecond)).1 ≤ Q0+Q1+1921 :=
  (VerifierCallBudget.firstReads_le_length _ _).trans
    (RawJ_AccountBudget.budget adapter current stage finish reserved query geo B std hashv copy allocator id adversary chooseSecond
      Q0 Q1 prefixBound choiceBound H)

theorem replay_queries
    (project : Outcome A → OraclePortCompactDraft.Parsed × (Fin 22 → Fin 262144))
    (H : Bytes → State) :
    firstReads emptyTable (eval H (SdkC_Replay.augmented
      (program adapter current stage finish reserved query geo B std hashv copy allocator id adversary chooseSecond) project)).1 ≤
      Q0+Q1+1921+1040 :=
  SdkC_Replay.augmented_bound _ project (Q0+Q1+1921)
    (first_reads adapter current stage finish reserved query geo B std hashv copy allocator id adversary chooseSecond Q0 Q1 prefixBound choiceBound) H

theorem replay_collision
    (project : Outcome A → OraclePortCompactDraft.Parsed × (Fin 22 → Fin 262144)) :
    lazyMean (SdkC_Replay.augmented
      (program adapter current stage finish reserved query geo B std hashv copy allocator id adversary chooseSecond) project) emptyTable
      (fun view => indicator (BinRawByteCollisionTargets.event
        SelectedTranscriptParams.params.iv (Q0+Q1+1921+1040) view)) ≤
      6 * ((Q0+Q1+1921+1040 : Nat) : Rat)^2 / (256^32 : Rat) :=
  SdkC_Replay.collision_bound _ project (Q0+Q1+1921)
    (first_reads adapter current stage finish reserved query geo B std hashv copy allocator id adversary chooseSecond Q0 Q1 prefixBound choiceBound)

#print axioms first_reads
#print axioms replay_queries
#print axioms replay_collision
end AspisR1.RawJ_CollisionBudget
end
