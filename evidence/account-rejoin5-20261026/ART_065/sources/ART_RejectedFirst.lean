import ART_AccountChronology
set_option autoImplicit false
noncomputable section
namespace AspisR1.ART_RejectedFirst
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open SCE_Experiment ARS_NativeAccount ART_PartialAccount

theorem no_second {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program) (a : Adversary A) (H : Bytes → State)
    (reject : ∀ saved post final,
      (eval H (wrapper hashv (firstSyntax c hashv copy allocator id (eval H a.first).2))).2 ≠
        ok (.Ok (saved,post,final))) :
    (eval H (ART_PartialAccount.account c hashv copy allocator id a)).2.2.2 = none ∧
    accepted (eval H (ART_PartialAccount.account c hashv copy allocator id a)).2 = false := by
  rw [ART_AccountChronology.first_reject c hashv copy allocator id a H reject]
  refine ⟨rfl,?_⟩
  cases (eval H (wrapper hashv (firstSyntax c hashv copy allocator id (eval H a.first).2))).2 with
  | fail error => rfl
  | div => rfl
  | ok result => cases result <;> rfl

#print axioms no_second
end AspisR1.ART_RejectedFirst
end
