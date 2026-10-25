import Hist_JointCharge
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hist_JointBinding
open FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8PairedCommitment
open OraclePortCompactDraft OraclePortSelectedDraft OraclePortBatchDraft

/-- P2Prime and the canonical replay are now charged against exactly one
containing log. This does not assert an association with a deployed source. -/
theorem binding_or_collision {A : Type} (iv : State) (source : Program Bytes State A)
    (prepare : A → Parsed × (Fin 22 → Fin 262144))
    (select : A → R9PoolRuntimeBinding.Inputs × R9PoolRuntimeBinding.Inputs) (Q : Nat)
    (sourceBudget : ∀ H : Bytes → State, firstReads emptyTable (eval H source).1 ≤ Q)
    (H : Bytes → State) :
    BinRawByteCollisionTargets.event iv (Q+1044) (eval H (Hist_JointCharge.joint source prepare select)) ∨
      R9PoolRuntimeBinding.P2Prime H (select (eval H source).2).1 (select (eval H source).2).2 := by
  have binding := Hist_ChargedBinding.binding_or_collision iv (SdkC_Replay.augmented source prepare)
    select (Q+1040) (SdkC_Replay.augmented_bound source prepare Q sourceBudget) H
  simpa [Hist_JointCharge.joint,Hist_JointCharge.replay_result,Nat.add_assoc] using binding

#print axioms binding_or_collision
end AspisR1.Hist_JointBinding
end
