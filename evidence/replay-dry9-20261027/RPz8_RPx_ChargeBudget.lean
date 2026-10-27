import RPz7_F3T_AccountCharge
set_option autoImplicit false
noncomputable section
namespace AspisR1.RPx_ChargeBudget
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw

theorem charge {A : Type} (source : Program Bytes State A) (Q : Nat)
    (queries : ∀ H : Bytes → State,(eval H source).1.length≤Q+1921)
    (project : A → OraclePortCompactDraft.Parsed × (Fin 22 → Fin 262144))
    (select : A → R9PoolRuntimeBinding.Inputs × R9PoolRuntimeBinding.Inputs) :
    (∀ H : Bytes → State,FS.firstReads FS.emptyTable
      (eval H (Hiq_RecordedJoint.program source project select)).1≤Q+2965) ∧
    F3T_AccountCharge.mass source project select Q≤F3T_Numeric.accountLoss Q := by
  have bound : ∀ H : Bytes → State,FS.firstReads FS.emptyTable (eval H source).1≤Q+1921 :=
    fun H=>(VerifierCallBudget.firstReads_le_length _ _).trans (queries H)
  exact ⟨F3T_AccountCharge.reads source project select Q bound,
    F3T_AccountCharge.bound source project select Q bound⟩

#print axioms charge
end AspisR1.RPx_ChargeBudget
end
