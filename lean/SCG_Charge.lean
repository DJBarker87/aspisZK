import SCE_AccountBound
import RPx_ChargeBudget
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCG_Charge
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open SCE_Experiment

/-- The ORIGINAL adaptive account, including every outer choice query, has
one Q0+Q1 envelope. No source/account event association is assumed here. -/
theorem charged {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)
    (a : Adversary A) (Q0 Q1 : Nat)
    (prefixBound : ∀ H, (eval H a.first).1.length ≤ Q0)
    (choiceBound : ∀ i saved post final H, (eval H (a.second i saved post final)).1.length ≤ Q1)
    (project : GExq_AccountExperiment.Outcome A → OraclePortCompactDraft.Parsed × (Fin 22 → Fin 262144))
    (select : GExq_AccountExperiment.Outcome A → R9PoolRuntimeBinding.Inputs × R9PoolRuntimeBinding.Inputs) :
    (∀ H, (eval H (account c hashv copy allocator id a)).1.length ≤ Q0+Q1+1921) ∧
    (∀ H, FS.firstReads FS.emptyTable
      (eval H (Hiq_RecordedJoint.program (account c hashv copy allocator id a) project select)).1
        ≤ Q0+Q1+2965) ∧
    F3T_AccountCharge.mass (account c hashv copy allocator id a) project select (Q0+Q1)
      ≤ F3T_Numeric.accountLoss (Q0+Q1) := by
  have budget := SCE_AccountBound.issued c hashv copy allocator id a Q0 Q1 prefixBound choiceBound
  exact ⟨budget, RPx_ChargeBudget.charge _ (Q0+Q1) budget project select⟩

#print axioms charged
end AspisR1.SCG_Charge
end
