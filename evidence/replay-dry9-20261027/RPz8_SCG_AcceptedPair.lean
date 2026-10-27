import RPz8_SCG_AcceptedExecution
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCG_AcceptedPair
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open SCE_Experiment SCE_Execution GExq_AccountExperiment

/-- Both IDEAL calls in the actual response-driven account, obtained from
its acceptance flag without choosing independent cuts or second inputs. -/
theorem replies {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)
    (a : Adversary A) (H : Bytes → State)
    (success : accepted (eval H (account c hashv copy allocator id a)).2 = true) :
    ∃ saved post final post2 final2,
      (eval H (firstCode c hashv copy allocator id (eval H a.first).2)).2 =
        ok (.Ok (saved,post,final)) ∧
      (eval H (secondCode c hashv allocator id
        (eval H (a.second (eval H a.first).2 saved post final)).2)).2 =
        ok (.Ok (post2,final2)) := by
  obtain ⟨saved,post,final,first⟩ :=
    SCG_AcceptedExecution.first_reply c hashv copy allocator id a H success
  rw [accepted_eval c hashv copy allocator id a H saved post final first] at success
  dsimp only at success
  rw [first] at success
  cases h : (eval H (secondCode c hashv allocator id
    (eval H (a.second (eval H a.first).2 saved post final)).2)).2 with
  | fail e => simp only [h,accepted] at success; cases success
  | div => simp only [h,accepted] at success; cases success
  | ok r =>
    cases r with
    | Err e => simp only [h,accepted] at success; cases success
    | Ok value =>
      rcases value with ⟨post2,final2⟩
      exact ⟨saved,post,final,post2,final2,first,h⟩

#print axioms replies
end AspisR1.SCG_AcceptedPair
end
