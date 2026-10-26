import RPx_AccountBudget
import F3T_AccountCharge
import GExq_AccountExperiment
import GExq_GlobalBudget
set_option autoImplicit false
noncomputable section
namespace AspisR1.RPx_AccountCharge
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers S2W_TrustedStd
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open GExq_AccountExperiment

theorem charged {A F C : Type} (adapter : AdapterRw.Ops) (ops : AspisR1CurrentCaller.Ops)
    (stage : VTop_Stages.Ops) (finish : AspisR1Stage2.Stage2Finish.FinishOps F)
    (reserved : Bool) (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)
    (adversary : Program Bytes State (FirstInputs A))
    (chooseSecond : FirstInputs A → alloc.vec.Vec U8 → Heap (Nat → Record) → A → Program Bytes State (SecondInputs A))
    (Q0 Q1 : Nat)
    (prefixBound : ∀ H : Bytes → State,(eval H adversary).1.length≤Q0)
    (choiceBound : ∀ input saved post final H,(eval H (chooseSecond input saved post final)).1.length≤Q1)
    (project : Outcome A → OraclePortCompactDraft.Parsed × (Fin 22 → Fin 262144))
    (select : Outcome A → R9PoolRuntimeBinding.Inputs × R9PoolRuntimeBinding.Inputs) :
    let account := program adapter ops stage finish reserved query geo B std hashv copy allocator id adversary chooseSecond
    (∀ H : Bytes → State,FS.firstReads FS.emptyTable
      (eval H (Hiq_RecordedJoint.program account project select)).1≤Q0+Q1+2965) ∧
    F3T_AccountCharge.mass account project select (Q0+Q1)≤F3T_Numeric.accountLoss (Q0+Q1) := by
  dsimp only
  have bound : ∀ H : Bytes → State,FS.firstReads FS.emptyTable
      (eval H (program adapter ops stage finish reserved query geo B std hashv
        copy allocator id adversary chooseSecond)).1≤(Q0+Q1)+1921 := by
    intro H
    exact (VerifierCallBudget.firstReads_le_length _ _).trans
      (RPx_AccountBudget.budget adapter ops stage finish reserved query geo B std hashv
        copy allocator id adversary chooseSecond Q0 Q1 prefixBound choiceBound H)
  exact ⟨F3T_AccountCharge.reads _ project select (Q0+Q1) bound,
    F3T_AccountCharge.bound _ project select (Q0+Q1) bound⟩

#print axioms charged
end AspisR1.RPx_AccountCharge
end
