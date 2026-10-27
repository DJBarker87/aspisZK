import RPz8_SCG_AcceptedShape
import RPz8_SCE_Execution
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCG_AcceptedExecution
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open SCE_Experiment SCE_Execution GExq_AccountExperiment

/-- Invert the ideal account flag on the very same response-selected
execution. Admissions and native execution are deliberately not outputs. -/
theorem first_reply {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)
    (a : Adversary A) (H : Bytes → State)
    (success : accepted (eval H (account c hashv copy allocator id a)).2 = true) :
    ∃ saved post final,
      (eval H (firstCode c hashv copy allocator id (eval H a.first).2)).2 =
        ok (.Ok (saved,post,final)) := by
  rw [account_def] at success
  simp only [eval_bind] at success
  cases h : (eval H (firstCode c hashv copy allocator id (eval H a.first).2)).2 with
  | fail e => simp only [h,eval,accepted] at success; cases success
  | div => simp only [h,eval,accepted] at success; cases success
  | ok r =>
    cases r with
    | Err e => simp only [h,eval,accepted] at success; cases success
    | Ok value =>
      rcases value with ⟨saved,post,final⟩
      exact ⟨saved,post,final,rfl⟩

#print axioms first_reply
end AspisR1.SCG_AcceptedExecution
end
