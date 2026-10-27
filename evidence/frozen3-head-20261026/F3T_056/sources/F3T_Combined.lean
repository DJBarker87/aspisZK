import F3T_AccountCharge
import F3T_ModelClaims
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3T_Combined
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open F3T_Experiment

theorem arithmetic (Q : Nat) : StartChargeNumeric.totalBound Q+F3T_Numeric.accountLoss Q=
    F3T_Numeric.total Q := by
  unfold StartChargeNumeric.totalBound F3T_Numeric.total F3T_Numeric.collisionLoss
    BinCombinedMerkleCollision.kappa
  rw [show (256:Rat)^32=2^256 by norm_num]
  ring

/-- A sum of two separately defined masses. No deployed union/event
association is asserted by this theorem. -/
theorem model_and_account {A : Type} (D : LiteralByteProtocol.Decoder) (P : Prover)
    (source : Program Bytes State A)
    (project : A → OraclePortCompactDraft.Parsed × (Fin 22 → Fin 262144))
    (select : A → R9PoolRuntimeBinding.Inputs × R9PoolRuntimeBinding.Inputs)
    (Q : Nat) (queries : ∀ H : Bytes → State,(eval H P).1.length≤Q)
    (sourceBudget : ∀ H,firstReads emptyTable (eval H source).1≤Q+1921) :
    F3T_ModelClaims.failure D P+F3T_AccountCharge.mass source project select Q≤F3T_Numeric.total Q :=
  (add_le_add (F3T_ModelClaims.failure_bound D P Q queries)
    (F3T_AccountCharge.bound source project select Q sourceBudget)).trans_eq (arithmetic Q)

theorem zero_queries {A : Type} (D : LiteralByteProtocol.Decoder) (P : Prover)
    (source : Program Bytes State A)
    (project : A → OraclePortCompactDraft.Parsed × (Fin 22 → Fin 262144))
    (select : A → R9PoolRuntimeBinding.Inputs × R9PoolRuntimeBinding.Inputs)
    (queries : ∀ H : Bytes → State,(eval H P).1.length≤0)
    (sourceBudget : ∀ H,firstReads emptyTable (eval H source).1≤0+1921) :
    F3T_ModelClaims.failure D P+F3T_AccountCharge.mass source project select 0<1/(2:Rat)^100 :=
  (model_and_account D P source project select 0 queries sourceBudget).trans_lt F3T_Numeric.zero_queries

#print axioms arithmetic
#print axioms model_and_account
#print axioms zero_queries
end AspisR1.F3T_Combined
end
