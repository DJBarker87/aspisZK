import RPz7_P2P_Charge
import RPz7_F3T_AccountCharge
set_option autoImplicit false
noncomputable section
namespace AspisR1.P2P_Accounting
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

/-- Both byte-identity guards use the very event measured by the account mass.
No second union summand or independence is required. -/
theorem single_event {X : Type} (source : Program Bytes State X)
    (project : X → OraclePortCompactDraft.Parsed × (Fin 22 → Fin 262144))
    (select : X → R9PoolRuntimeBinding.Inputs × R9PoolRuntimeBinding.Inputs)
    (Q : Nat) (budget : ∀ H, firstReads emptyTable (eval H source).1 ≤ Q+1921) :
    (∀ H, BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (Q+2965)
      (eval H (Hiq_RecordedJoint.program source project select)) ∨
      R9PoolRuntimeBinding.P2Prime H (select (eval H source).2).1 (select (eval H source).2).2) ∧
    F3T_AccountCharge.mass source project select Q ≤
      6*((Q+2965:Nat):Rat)^2/(2:Rat)^256 := by
  exact ⟨P2P_Charge.binding_or_collision source project select Q budget,
    F3T_AccountCharge.bound source project select Q budget⟩

theorem allowance : (1921:Nat)+1040+4=2965 := rfl

#print axioms single_event
#print axioms allowance
end AspisR1.P2P_Accounting
end
