import RPz7_Hiq_RecordedBudget
import RPz7_F3T_Numeric
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3T_AccountCharge
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.CausalFirstHitUnionBound

def mass {A : Type} (source : Program Bytes State A)
    (project : A → OraclePortCompactDraft.Parsed × (Fin 22 → Fin 262144))
    (select : A → R9PoolRuntimeBinding.Inputs × R9PoolRuntimeBinding.Inputs) (Q : Nat) : Rat :=
  lazyMean (Hiq_RecordedJoint.program source project select) emptyTable
    (fun v => indicator (BinRawByteCollisionTargets.event SelectedTranscriptParams.params.iv (Q+2965) v))

theorem reads {A : Type} (source : Program Bytes State A)
    (project : A → OraclePortCompactDraft.Parsed × (Fin 22 → Fin 262144))
    (select : A → R9PoolRuntimeBinding.Inputs × R9PoolRuntimeBinding.Inputs)
    (Q : Nat) (budget : ∀ H,firstReads emptyTable (eval H source).1≤Q+1921) (H : Bytes → State) :
    firstReads emptyTable (eval H (Hiq_RecordedJoint.program source project select)).1≤Q+2965 := by
  simpa only [Nat.add_assoc] using Hiq_RecordedBudget.queries source project select (Q+1921) budget H

theorem bound {A : Type} (source : Program Bytes State A)
    (project : A → OraclePortCompactDraft.Parsed × (Fin 22 → Fin 262144))
    (select : A → R9PoolRuntimeBinding.Inputs × R9PoolRuntimeBinding.Inputs)
    (Q : Nat) (budget : ∀ H,firstReads emptyTable (eval H source).1≤Q+1921) :
    mass source project select Q≤F3T_Numeric.accountLoss Q := by
  have b := Hiq_RecordedBudget.collision source project select (Q+1921) budget
  simpa only [mass,F3T_Numeric.accountLoss,Nat.add_assoc,show (256:Rat)^32=2^256 by norm_num] using b

#print axioms reads
#print axioms bound
end AspisR1.F3T_AccountCharge
end
