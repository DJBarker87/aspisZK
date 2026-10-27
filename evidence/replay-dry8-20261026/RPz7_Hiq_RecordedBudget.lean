import RPz7_Hiq_RecordedJoint
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hiq_RecordedBudget
open FS FS2 FS2.Duplex AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.CausalFirstHitUnionBound

theorem queries {A : Type} (source : Program Bytes State A)
    (project : A → OraclePortCompactDraft.Parsed × (Fin 22 → Fin 262144))
    (select : A → R9PoolRuntimeBinding.Inputs × R9PoolRuntimeBinding.Inputs)
    (Q : Nat) (budget : ∀ H : Bytes → State, firstReads emptyTable (eval H source).1 ≤ Q)
    (H : Bytes → State) :
    firstReads emptyTable (eval H (Hiq_RecordedJoint.program source project select)).1 ≤ Q+1044 := by
  rw [Hiq_RecordedJoint.evaluation]
  exact Hist_JointCharge.budget source project select Q budget H

theorem collision {A : Type} (source : Program Bytes State A)
    (project : A → OraclePortCompactDraft.Parsed × (Fin 22 → Fin 262144))
    (select : A → R9PoolRuntimeBinding.Inputs × R9PoolRuntimeBinding.Inputs)
    (Q : Nat) (budget : ∀ H : Bytes → State, firstReads emptyTable (eval H source).1 ≤ Q) :
    lazyMean (Hiq_RecordedJoint.program source project select) emptyTable
      (fun v => indicator (BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (Q+1044) v)) ≤
      6*((Q+1044 : Nat) : Rat)^2/(256^32 : Rat) :=
  BinRawByteCollisionTargets.mass _ _ _ (queries source project select Q budget)

#print axioms queries
#print axioms collision
end AspisR1.Hiq_RecordedBudget
end
