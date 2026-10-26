import ARS_NativeCost
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARS_NativeOutcome
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw SCE_Experiment GExq_AccountExperiment

variable {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program) (a : Adversary A)
    (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)

/-- Direct partial native wrapper outcome, with the original adaptive choices. -/
def wrappers (native : Bytes → State) : Outcome A :=
  let i := (eval native a.first).2
  let reply := first native1 copy allocator i.entry id i.data i.state
  match reply with
  | .ok (.Ok (saved,post,final)) =>
    let j := (eval native (a.second i saved post final)).2
    (i,reply,some (j,second native2 allocator j.entry id j.data j.slot j.state))
  | _ => (i,reply,none)

/-- This source/native outcome relation includes syscall failures and pure
rejection, without an ideal-oracle representation assertion for failed calls. -/
theorem source (native : Bytes → State)
    (extraction : S2W_DigestExtraction.AeneasExtraction
      (GExq_Caller.sdk c.adapter c.currentBase c.stageBase c.finish c.reserved
        c.query c.geometry c.boundaries c.std) native1 native2 hashv) :
    (ARS_NativeAccount.run c hashv copy allocator id a native).2 =
      wrappers copy allocator id a native1 native2 native := by
  have one : (SdkC_Source.run hashv
      (ARS_NativeAccount.firstSyntax c hashv copy allocator id (eval native a.first).2) []).1 =
      first native1 copy allocator (eval native a.first).2.entry id
        (eval native a.first).2.data (eval native a.first).2.state :=
    (SdkC_Source.erasure hashv _ []).trans
      (GExq_InstalledWrapper.first_source c.adapter c.currentBase c.stageBase c.finish c.reserved
        c.query c.geometry c.boundaries c.std hashv copy allocator _ id _ _ native1 native2 extraction)
  have two : ∀ j : SecondInputs A,
      (SdkC_Source.run hashv (ARS_NativeAccount.secondSyntax c hashv allocator id j) []).1 =
        second native2 allocator j.entry id j.data j.slot j.state := by
    intro j
    exact (SdkC_Source.erasure hashv _ []).trans
      (GExq_InstalledWrapper.second_source c.adapter c.currentBase c.stageBase c.finish c.reserved
        c.query c.geometry c.boundaries c.std hashv allocator _ id _ _ _ native1 native2 extraction)
  unfold ARS_NativeAccount.run wrappers
  dsimp only
  rw [one]
  cases reply : first native1 copy allocator (eval native a.first).2.entry id
      (eval native a.first).2.data (eval native a.first).2.state with
  | fail error => rfl
  | div => rfl
  | ok result =>
    cases result with
    | Err error => rfl
    | Ok value =>
      rcases value with ⟨saved,post,final⟩
      simp only [two]

#print axioms source
end AspisR1.ARS_NativeOutcome
end
