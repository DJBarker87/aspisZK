import GExp_GlobalBudget
import SdkC_Replay
set_option autoImplicit false
noncomputable section
namespace AspisR1.GExp_CollisionBudget
open Aeneas Aeneas.Std Result GExp_Experiment
open FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.CausalFirstHitUnionBound
variable (current : AspisR1CurrentCaller.Ops) (stage : VTop_Stages.Ops) (reserved : Bool)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (D1 : AspisR1CurrentCaller.aspis_core.digest.Digest32 Unit)
    (D2 : VTop_Stages.aspis_core.digest.Digest32 Unit)
    (adversary : Program Bytes State FirstInputs)
    (chooseSecond : FirstInputs → alloc.vec.Vec U8 → Program Bytes State SecondInputs)
    (Q0 Q1 : Nat)
    (prefixBound : ∀ H, (eval H adversary).1.length ≤ Q0)
    (choiceBound : ∀ input saved H, (eval H (chooseSecond input saved)).1.length ≤ Q1)

include prefixBound choiceBound

theorem first_reads (H : Bytes → State) :
    firstReads emptyTable
      (eval H (program current stage reserved B std hashv D1 D2 adversary chooseSecond)).1 ≤ Q0+Q1+22585 :=
  (VerifierCallBudget.firstReads_le_length _ _).trans
    (GExp_GlobalBudget.budget current stage reserved B std hashv D1 D2 adversary chooseSecond
      Q0 Q1 prefixBound choiceBound H)

theorem replay_queries
    (project : Outcome → OraclePortCompactDraft.Parsed × (Fin 22 → Fin 262144))
    (H : Bytes → State) :
    firstReads emptyTable (eval H (SdkC_Replay.augmented
      (program current stage reserved B std hashv D1 D2 adversary chooseSecond) project)).1 ≤
      Q0+Q1+22585+1040 :=
  SdkC_Replay.augmented_bound _ project (Q0+Q1+22585)
    (first_reads current stage reserved B std hashv D1 D2 adversary chooseSecond Q0 Q1 prefixBound choiceBound) H

theorem replay_collision
    (project : Outcome → OraclePortCompactDraft.Parsed × (Fin 22 → Fin 262144)) :
    lazyMean (SdkC_Replay.augmented
      (program current stage reserved B std hashv D1 D2 adversary chooseSecond) project) emptyTable
      (fun view => indicator (BinRawByteCollisionTargets.event
        SelectedTranscriptParams.params.iv (Q0+Q1+22585+1040) view)) ≤
      6 * ((Q0+Q1+22585+1040 : Nat) : Rat)^2 / (256^32 : Rat) :=
  SdkC_Replay.collision_bound _ project (Q0+Q1+22585)
    (first_reads current stage reserved B std hashv D1 D2 adversary chooseSecond Q0 Q1 prefixBound choiceBound)

#print axioms first_reads
#print axioms replay_queries
#print axioms replay_collision
end AspisR1.GExp_CollisionBudget
end
