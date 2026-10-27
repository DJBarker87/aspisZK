import RPz7_Hiq_AccountAudit
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hiq_JointBinding
open FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8PairedCommitment

theorem binding_or_collision {A : Type} (iv : State) (source : Program Bytes State A)
    (project : A → OraclePortCompactDraft.Parsed × (Fin 22 → Fin 262144))
    (select : A → R9PoolRuntimeBinding.Inputs × R9PoolRuntimeBinding.Inputs) (Q : Nat)
    (budget : ∀ H : Bytes → State, firstReads emptyTable (eval H source).1 ≤ Q)
    (H : Bytes → State) :
    BinRawByteCollisionTargets.event iv (Q+1044) (eval H (Hist_JointCharge.joint source project select)) ∨
      R9PoolRuntimeBinding.P2Prime H (select (eval H source).2).1 (select (eval H source).2).2 := by
  have h := Hist_ChargedBinding.binding_or_collision iv (SdkC_Replay.augmented source project) select
    (Q+1040) (SdkC_Replay.augmented_bound source project Q budget) H
  rw [Hist_JointCharge.replay_result] at h
  simpa only [Hist_JointCharge.joint,show Q+1040+4 = Q+1044 by omega] using h

#print axioms binding_or_collision
end AspisR1.Hiq_JointBinding
end
