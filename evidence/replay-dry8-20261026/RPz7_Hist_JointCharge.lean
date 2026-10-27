import RPz7_Hist_ByteExperiment
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hist_JointCharge
open FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8PairedCommitment
open OraclePortCompactDraft OraclePortSelectedDraft OraclePortBatchDraft
open AspisV8R19.CausalFirstHitUnionBound
open MultiproofConeCanonical S2W_NativeConsolidation

/-- One enlarged experiment, charging both canonical replay and all four
byte-string audit reads after the unchanged source prefix. -/
def joint {A : Type} (source : Program Bytes State A)
    (prepare : A → Parsed × (Fin 22 → Fin 262144))
    (select : A → R9PoolRuntimeBinding.Inputs × R9PoolRuntimeBinding.Inputs) : Program Bytes State A :=
  Hist_AuditQueries.augmented (SdkC_Replay.augmented source prepare) select

theorem replay_result {A : Type} (H : Bytes → State) (source : Program Bytes State A)
    (prepare : A → Parsed × (Fin 22 → Fin 262144)) :
    (eval H (SdkC_Replay.augmented source prepare)).2 = (eval H source).2 := by
  simp only [SdkC_Replay.augmented,eval_bind,eval]

theorem same_result {A : Type} (H : Bytes → State) (source : Program Bytes State A)
    (prepare : A → Parsed × (Fin 22 → Fin 262144))
    (select : A → R9PoolRuntimeBinding.Inputs × R9PoolRuntimeBinding.Inputs) :
    (eval H (joint source prepare select)).2 = (eval H source).2 :=
  (Hist_ChargedBinding.result_preserved H _ select).trans (replay_result H source prepare)

theorem budget {A : Type} (source : Program Bytes State A)
    (prepare : A → Parsed × (Fin 22 → Fin 262144))
    (select : A → R9PoolRuntimeBinding.Inputs × R9PoolRuntimeBinding.Inputs) (Q : Nat)
    (sourceBudget : ∀ H : Bytes → State, firstReads emptyTable (eval H source).1 ≤ Q)
    (H : Bytes → State) : firstReads emptyTable (eval H (joint source prepare select)).1 ≤ Q+1044 := by
  have h := Hist_AuditQueries.augmented_budget (SdkC_Replay.augmented source prepare) select (Q+1040)
    (SdkC_Replay.augmented_bound source prepare Q sourceBudget) H
  simpa [joint,Nat.add_assoc] using h

theorem collision_bound {A : Type} (iv : State) (source : Program Bytes State A)
    (prepare : A → Parsed × (Fin 22 → Fin 262144))
    (select : A → R9PoolRuntimeBinding.Inputs × R9PoolRuntimeBinding.Inputs) (Q : Nat)
    (sourceBudget : ∀ H : Bytes → State, firstReads emptyTable (eval H source).1 ≤ Q) :
    lazyMean (joint source prepare select) emptyTable
      (fun view => indicator (BinRawByteCollisionTargets.event iv (Q+1044) view)) ≤
      6 * ((Q+1044 : Nat) : Rat)^2 / (256^32 : Rat) :=
  BinRawByteCollisionTargets.mass iv (Q+1044) _ (budget source prepare select Q sourceBudget)

#print axioms replay_result
#print axioms same_result
#print axioms budget
#print axioms collision_bound
end AspisR1.Hist_JointCharge
end
