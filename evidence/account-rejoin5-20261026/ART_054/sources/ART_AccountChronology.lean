import ART_PartialAccount
set_option autoImplicit false
noncomputable section
namespace AspisR1.ART_AccountChronology
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open GExq_AccountExperiment SCE_Experiment ARS_NativeAccount ART_PartialAccount
variable {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program) (a : Adversary A)

theorem first_ok (H : Bytes → State) (saved : alloc.vec.Vec U8) (post : Heap (Nat → Record)) (final : A)
    (first : (eval H (wrapper hashv (firstSyntax c hashv copy allocator id (eval H a.first).2))).2 =
      ok (.Ok (saved,post,final))) :
    let i := eval H a.first
    let f := eval H (wrapper hashv (firstSyntax c hashv copy allocator id i.2))
    let j := eval H (a.second i.2 saved post final)
    let s := eval H (wrapper hashv (secondSyntax c hashv allocator id j.2))
    eval H (ART_PartialAccount.account c hashv copy allocator id a) =
      (i.1 ++ (f.1 ++ (j.1 ++ s.1)),(i.2,f.2,some (j.2,s.2))) := by
  simp only [ART_PartialAccount.account,eval_bind,first,eval,List.append_nil]

theorem first_reject (H : Bytes → State)
    (reject : ∀ saved post final,
      (eval H (wrapper hashv (firstSyntax c hashv copy allocator id (eval H a.first).2))).2 ≠
        ok (.Ok (saved,post,final))) :
    let i := eval H a.first
    let f := eval H (wrapper hashv (firstSyntax c hashv copy allocator id i.2))
    eval H (ART_PartialAccount.account c hashv copy allocator id a) = (i.1 ++ f.1,(i.2,f.2,none)) := by
  unfold ART_PartialAccount.account
  simp only [eval_bind]
  split
  · rename_i saved post final same
    exact False.elim (reject saved post final same)
  · simp only [eval,List.append_nil]

#print axioms first_ok
#print axioms first_reject
end AspisR1.ART_AccountChronology
end
