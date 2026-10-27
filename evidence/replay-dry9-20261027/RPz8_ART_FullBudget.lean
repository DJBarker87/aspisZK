import RPz8_ART_WrapperBudget
set_option autoImplicit false
noncomputable section
namespace AspisR1.ART_FullBudget
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open SCE_Experiment ARS_NativeAccount ART_PartialAccount

/-- A SINGLE bound on total reached adversary work suffices: Q+1921 issued
calls on every outcome, without Q per submission or Q+68 starts. -/
theorem issued {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program) (a : Adversary A)
    (Q : Nat) (bound : ART_AdversaryWork.Bound c hashv copy allocator id a Q) (H : Bytes → State) :
    (eval H (ART_PartialAccount.account c hashv copy allocator id a)).1.length ≤ Q+1921 := by
  have total := bound H
  unfold ART_AdversaryWork.work at total
  have firstCost := ART_WrapperBudget.first c hashv copy allocator id (eval H a.first).2 H
  unfold ART_PartialAccount.account
  simp only [eval_bind]
  cases reply : (eval H (wrapper hashv (firstSyntax c hashv copy allocator id (eval H a.first).2))).2 with
  | fail error => simp only [reply,Nat.add_zero] at total; simp only [eval,List.length_append,List.length_nil]; omega
  | div => simp only [reply,Nat.add_zero] at total; simp only [eval,List.length_append,List.length_nil]; omega
  | ok result =>
    cases result with
    | Err error => simp only [reply,Nat.add_zero] at total; simp only [eval,List.length_append,List.length_nil]; omega
    | Ok value =>
      rcases value with ⟨saved,post,final⟩
      simp only [reply] at total
      have secondCost := ART_WrapperBudget.second c hashv allocator id
        (eval H (a.second (eval H a.first).2 saved post final)).2 H
      simp only [eval_bind,eval,List.length_append,List.length_nil]
      omega

#print axioms issued
end AspisR1.ART_FullBudget
end
