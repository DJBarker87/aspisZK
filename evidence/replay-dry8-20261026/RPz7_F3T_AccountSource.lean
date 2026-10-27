import RPz7_RawJ_CollisionBudget
import RPz7_F3T_AccountCharge
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3T_AccountSource
open Aeneas Aeneas.Std Result GExq_AccountExperiment S2Trust S2W_D189Entry S2W_D189Wrappers
open FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.CausalFirstHitUnionBound
variable {A F C : Type} (adapter : AdapterRw.Ops) (current : AspisR1CurrentCaller.Ops)
    (stage : VTop_Stages.Ops) (finish : AspisR1Stage2.Stage2Finish.FinishOps F) (reserved : Bool)
    (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops C)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)
    (adversary : Program Bytes State (FirstInputs A))
    (chooseSecond : FirstInputs A → alloc.vec.Vec U8 → Heap (Nat → Record) → A → Program Bytes State (SecondInputs A))
    (Q0 Q1 : Nat)
    (prefixBound : ∀ H, (eval H adversary).1.length ≤ Q0)
    (choiceBound : ∀ input saved post final H, (eval H (chooseSecond input saved post final)).1.length ≤ Q1)

include prefixBound choiceBound

theorem account_bound
    (project : Outcome A → OraclePortCompactDraft.Parsed × (Fin 22 → Fin 262144))
    (select : Outcome A → R9PoolRuntimeBinding.Inputs × R9PoolRuntimeBinding.Inputs) :
    F3T_AccountCharge.mass
      (program adapter current stage finish reserved query geo B std hashv copy allocator id adversary chooseSecond)
      project select (Q0+Q1) ≤ F3T_Numeric.accountLoss (Q0+Q1) :=
  F3T_AccountCharge.bound _ project select (Q0+Q1)
    (RawJ_CollisionBudget.first_reads adapter current stage finish reserved query geo B std hashv
      copy allocator id adversary chooseSecond Q0 Q1 prefixBound choiceBound)

#print axioms account_bound
end AspisR1.F3T_AccountSource
end
