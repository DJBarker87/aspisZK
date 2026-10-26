import ARS_NativeAccount
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARS_NativeCost
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open ARS_NativeAccount SCE_Experiment

/-- No duplicate or rejected-prefix discount in readLog on this exact class. -/
theorem read_count (log : SdkC_Source.Log) (returns : ARR_ReturnCoverage.ReturnsOnly log) :
    (SdkC_Source.readLog log).length = log.length := by
  induction log with
  | nil => rfl
  | cons q tail ih =>
    obtain ⟨digest,returned⟩ := returns q (List.mem_cons_self ..)
    simp only [SdkC_Source.readLog,List.filterMap_cons,returned,List.length_cons]
    exact congrArg Nat.succ (ih (fun x member => returns x (List.mem_cons_of_mem _ member)))

/-- Original attempted syscall cost, first-prefix/adaptive-choice requests and
all duplicates are preserved through every represented rejection path. -/
theorem exact {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program) (a : Adversary A)
    (native H : Bytes → State)
    (certificate : Certificate c hashv copy allocator id a native H) :
    (eval H (account c hashv copy allocator id a)).1.length =
      attempts c hashv copy allocator id a native := by
  rw [ARS_NativeAccount.exact c hashv copy allocator id a native H certificate]
  obtain ⟨_,firstCovered,secondCovered⟩ := certificate
  have firstReturns := ARR_ReturnCoverage.returns_of_covered H hashv _ firstCovered []
    (by intro q member; cases member)
  have firstCount := read_count _ firstReturns
  unfold ARS_NativeAccount.run attempts
  dsimp only
  cases reply : (SdkC_Source.run hashv (firstSyntax c hashv copy allocator id (eval native a.first).2) []).1 with
  | fail error => simp only [reply,List.length_append,firstCount]
  | div => simp only [reply,List.length_append,firstCount]
  | ok result =>
    cases result with
    | Err error => simp only [reply,List.length_append,firstCount]
    | Ok value =>
      rcases value with ⟨saved,post,final⟩
      have secondReturns := ARR_ReturnCoverage.returns_of_covered H hashv _
        (secondCovered saved post final reply).2 [] (by intro q member; cases member)
      have secondCount := read_count _ secondReturns
      simp only [reply,List.length_append,firstCount,secondCount]

#print axioms read_count
#print axioms exact
end AspisR1.ARS_NativeCost
end
