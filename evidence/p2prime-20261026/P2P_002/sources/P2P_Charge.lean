import Hiq_JointBinding
import F3T_AccountCharge
set_option autoImplicit false
noncomputable section
namespace AspisR1.P2P_Charge
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw

/-- The four binding reads are already included in 2965: 1921+1040+4.
This is the literal existing charged event, without a second loss. -/
theorem binding_or_collision {A : Type} (source : Program Bytes State A)
    (project : A → OraclePortCompactDraft.Parsed × (Fin 22 → Fin 262144))
    (select : A → R9PoolRuntimeBinding.Inputs × R9PoolRuntimeBinding.Inputs)
    (Q : Nat) (budget : ∀ H, firstReads emptyTable (eval H source).1 ≤ Q+1921)
    (H : Bytes → State) :
    BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (Q+2965)
      (eval H (Hiq_RecordedJoint.program source project select)) ∨
    R9PoolRuntimeBinding.P2Prime H (select (eval H source).2).1
      (select (eval H source).2).2 := by
  have alternative := Hiq_JointBinding.binding_or_collision SelectedTranscriptParams.params.iv
    source project select (Q+1921) budget H
  rw [Hiq_RecordedJoint.evaluation]
  simpa only [BinRawByteCollisionTargets.event, Nat.add_assoc] using alternative

/-- Any consumer of this pair binding is transported through the SAME event.
The consumer is a proof transformation, never an added source assumption. -/
theorem consume {A : Type} (source : Program Bytes State A)
    (project : A → OraclePortCompactDraft.Parsed × (Fin 22 → Fin 262144))
    (select : A → R9PoolRuntimeBinding.Inputs × R9PoolRuntimeBinding.Inputs)
    (Q : Nat) (budget : ∀ H, firstReads emptyTable (eval H source).1 ≤ Q+1921)
    (H : Bytes → State) (C : Prop)
    (consumer : R9PoolRuntimeBinding.P2Prime H (select (eval H source).2).1
      (select (eval H source).2).2 → C) :
    BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (Q+2965)
      (eval H (Hiq_RecordedJoint.program source project select)) ∨ C :=
  (binding_or_collision source project select Q budget H).imp_right consumer

#print axioms binding_or_collision
#print axioms consume
end AspisR1.P2P_Charge
end
