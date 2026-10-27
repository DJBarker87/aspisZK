import RPz7_GExq_GlobalBudget
import RPz7_RawJ_InstalledBudget
import RPz7_GExq_AccountExperiment
set_option autoImplicit false
noncomputable section
namespace AspisR1.RawJ_AccountBudget
open Aeneas Aeneas.Std Result
open GExq_AccountExperiment S2Trust S2W_D189Entry S2W_D189Wrappers S2W_TrustedStd
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

theorem budget {A F C : Type} (adapter : AdapterRw.Ops) (current : AspisR1CurrentCaller.Ops)
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
    (H : Bytes → State) :
    (eval H (program adapter current stage finish reserved query geo B std hashv copy allocator id adversary chooseSecond)).1.length ≤
      Q0+Q1+1921 := by
  unfold program
  apply (GExq_GlobalBudget.bind_length _ _ H Q0 (1018+(Q1+903)) (prefixBound H) ?_).trans
  · omega
  intro input
  apply GExq_GlobalBudget.bind_length _ _ H 1018 (Q1+903)
  · exact RawJ_InstalledBudget.first adapter current stage finish reserved query geo B std hashv copy allocator _ id _ _ H
  intro reply
  cases reply with
  | fail e => exact Nat.zero_le _
  | div => exact Nat.zero_le _
  | ok r => cases r with
    | Err e => exact Nat.zero_le _
    | Ok value =>
      rcases value with ⟨saved,post,final⟩
      apply GExq_GlobalBudget.bind_length _ _ H Q1 903 (choiceBound input saved post final H)
      intro next
      apply (GExq_GlobalBudget.bind_length _ _ H 903 0 ?_ (fun _ => Nat.zero_le _)).trans
      · omega
      exact RawJ_InstalledBudget.second adapter current stage finish reserved query geo B std hashv allocator _ id _ _ _ H

#print axioms budget
end AspisR1.RawJ_AccountBudget
end
