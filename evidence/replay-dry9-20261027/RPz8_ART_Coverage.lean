import RPz8_ART_WrapperExact
set_option autoImplicit false
noncomputable section
namespace AspisR1.ART_Coverage
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open GExq_AccountExperiment SCE_Experiment ARS_NativeAccount ART_PartialAccount

/-- Exact partial-source coverage, including rejected syscalls. Original
adaptive choices, raw native outcomes, and every attempted call are retained.
This is not yet all-world bank support for the total-oracle account. -/
theorem execution {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program) (a : Adversary A)
    (native H : Bytes → State)
    (certificate : ART_PartialAccount.Certificate c hashv copy allocator id a native H) :
    eval H (ART_PartialAccount.account c hashv copy allocator id a) =
      represented c hashv copy allocator id a native H := by
  obtain ⟨prefixAgrees,firstAgrees,secondAgrees⟩ := certificate
  have firstChoice := ARS_AccountReplay.replay a.first native H prefixAgrees
  have firstSame := ART_WrapperExact.execution hashv H
    (firstSyntax c hashv copy allocator id (eval native a.first).2) firstAgrees
  unfold ART_PartialAccount.account
  simp only [eval_bind,firstChoice,firstSame]
  unfold represented
  dsimp only
  cases reply : (SdkC_Source.run hashv (firstSyntax c hashv copy allocator id (eval native a.first).2) []).1 with
  | fail error => simp only [reply,eval,List.append_nil]
  | div => simp only [reply,eval,List.append_nil]
  | ok result =>
    cases result with
    | Err error => simp only [reply,eval,List.append_nil]
    | Ok value =>
      rcases value with ⟨saved,post,final⟩
      obtain ⟨choice,agrees⟩ := secondAgrees saved post final reply
      have choiceSame := ARS_AccountReplay.replay _ native H choice
      have secondSame := ART_WrapperExact.execution hashv H
        (secondSyntax c hashv allocator id (eval native (a.second (eval native a.first).2 saved post final)).2) agrees
      simp only [reply,eval_bind,choiceSame,secondSame,eval,List.append_nil]

#print axioms execution
end AspisR1.ART_Coverage
end
