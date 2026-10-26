import ART_WrapperAccepted
import SCE_Execution
set_option autoImplicit false
noncomputable section
namespace AspisR1.ART_AccountAccepted
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open SCE_Experiment SCE_Execution ARS_NativeAccount

/-- No success-only coverage premise is added: failure-aware acceptance itself
selects the two successful wrappers and hence exactly the old ideal account. -/
theorem exact {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program) (a : Adversary A)
    (H : Bytes → State)
    (accepted : SCE_Experiment.accepted
      (eval H (ART_PartialAccount.account c hashv copy allocator id a)).2 = true) :
    eval H (ART_PartialAccount.account c hashv copy allocator id a) =
      eval H (SCE_Experiment.account c hashv copy allocator id a) := by
  have expanded := accepted
  unfold ART_PartialAccount.account at expanded ⊢
  rw [SCE_Execution.account_def]
  simp only [eval_bind] at expanded ⊢
  cases firstReply : (eval H (ART_PartialAccount.wrapper hashv
      (firstSyntax c hashv copy allocator id (eval H a.first).2))).2 with
  | fail error => simp only [firstReply,eval,SCE_Experiment.accepted] at expanded; cases expanded
  | div => simp only [firstReply,eval,SCE_Experiment.accepted] at expanded; cases expanded
  | ok result =>
    cases result with
    | Err error => simp only [firstReply,eval,SCE_Experiment.accepted] at expanded; cases expanded
    | Ok value =>
      rcases value with ⟨saved,post,final⟩
      have firstSame := ART_WrapperAccepted.exact hashv H
        (firstSyntax c hashv copy allocator id (eval H a.first).2) _ firstReply
      change eval H (ART_PartialAccount.wrapper hashv
        (firstSyntax c hashv copy allocator id (eval H a.first).2)) =
        eval H (firstCode c hashv copy allocator id (eval H a.first).2) at firstSame
      rw [←firstSame]
      simp only [firstReply,eval_bind] at expanded ⊢
      cases secondReply : (eval H (ART_PartialAccount.wrapper hashv
          (secondSyntax c hashv allocator id
            (eval H (a.second (eval H a.first).2 saved post final)).2))).2 with
      | fail error => simp only [secondReply,eval,SCE_Experiment.accepted] at expanded; cases expanded
      | div => simp only [secondReply,eval,SCE_Experiment.accepted] at expanded; cases expanded
      | ok result =>
        cases result with
        | Err error => simp only [secondReply,eval,SCE_Experiment.accepted] at expanded; cases expanded
        | Ok value =>
          have secondSame := ART_WrapperAccepted.exact hashv H
            (secondSyntax c hashv allocator id
              (eval H (a.second (eval H a.first).2 saved post final)).2) value secondReply
          change eval H (ART_PartialAccount.wrapper hashv
            (secondSyntax c hashv allocator id
              (eval H (a.second (eval H a.first).2 saved post final)).2)) =
            eval H (secondCode c hashv allocator id
              (eval H (a.second (eval H a.first).2 saved post final)).2) at secondSame
          rw [←secondSame]

#print axioms exact
end AspisR1.ART_AccountAccepted
end
