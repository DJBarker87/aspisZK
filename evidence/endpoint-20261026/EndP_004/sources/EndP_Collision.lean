import EndP_Numeric
import GExp_CollisionBudget
import AuS1_Finish
set_option autoImplicit false
noncomputable section
namespace AspisR1.EndP_Collision
open Aeneas Aeneas.Std Result FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.CausalFirstHitUnionBound

/-- The EXACT AuS1 alternative on the source trace and selected replay.
This identity does not assert that two different source traces are equal. -/
theorem alternative {A : Type} (source : Program Bytes State A)
    (project : A → OraclePortCompactDraft.Parsed × (Fin 22 → Fin 262144))
    (H : Bytes → State) :
    AuS1_Finish.Collision H (eval H source).1 (project (eval H source).2).1
      (project (eval H source).2).2 ↔
    BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv
      (firstReads emptyTable (eval H source).1+1040)
      (eval H (SdkC_Replay.augmented source project)) := by
  simp only [AuS1_Finish.Collision,BinRawByteCollisionTargets.event,
    SdkC_Replay.augmented,eval_bind,eval,List.append_nil]

/-- The original AuS1 probability law with the WHOLE source budget charged.
Instantiation with GExp's source budget yields Q+23625, not Q+1040. -/
theorem loss {A : Type} (source : Program Bytes State A)
    (project : A → OraclePortCompactDraft.Parsed × (Fin 22 → Fin 262144))
    (Q : Nat)
    (budget : ∀ H : Bytes → State, firstReads emptyTable (eval H source).1 ≤ Q+22585) :
    lazyMean (SdkC_Replay.augmented source project) emptyTable
      (fun view => indicator (BinRawByteCollisionTargets.event
        SelectedTranscriptParams.params.iv (Q+23625) view)) ≤ EndP_Numeric.authLoss Q := by
  have bound := AuS1_Bound.collision_loss source project (Q+22585) budget
  rw [EndP_Numeric.replay_loss] at bound
  simpa only [show Q+22585+1040 = Q+23625 by omega] using bound

variable (current : AspisR1CurrentCaller.Ops) (stage : VTop_Stages.Ops) (reserved : Bool)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (D1 : AspisR1CurrentCaller.aspis_core.digest.Digest32 Unit)
    (D2 : VTop_Stages.aspis_core.digest.Digest32 Unit)
    (adversary : Program Bytes State GExp_Experiment.FirstInputs)
    (chooseSecond : GExp_Experiment.FirstInputs → alloc.vec.Vec U8 →
      Program Bytes State GExp_Experiment.SecondInputs)
    (Q0 Q1 : Nat)
    (prefixBound : ∀ H, (eval H adversary).1.length ≤ Q0)
    (choiceBound : ∀ input saved H, (eval H (chooseSecond input saved)).1.length ≤ Q1)
    (project : GExp_Experiment.Outcome → OraclePortCompactDraft.Parsed × (Fin 22 → Fin 262144))

include prefixBound choiceBound
/-- Concrete existing GExp instance; no new uniform-budget assumption. -/
theorem global_loss :
    lazyMean (SdkC_Replay.augmented
      (GExp_Experiment.program current stage reserved B std hashv D1 D2 adversary chooseSecond) project)
      emptyTable (fun view => indicator (BinRawByteCollisionTargets.event
        SelectedTranscriptParams.params.iv (Q0+Q1+23625) view)) ≤
      6*((Q0+Q1+23625 : Nat) : Rat)^2/(2:Rat)^256 :=
  loss _ project (Q0+Q1)
    (GExp_CollisionBudget.first_reads current stage reserved B std hashv D1 D2 adversary chooseSecond
      Q0 Q1 prefixBound choiceBound)

#print axioms alternative
#print axioms loss
#print axioms global_loss
end AspisR1.EndP_Collision
end
