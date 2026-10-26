import ARS_QueryCost
import ARS_AccountReplay
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARS_NativeAccount
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open SCE_Experiment GExq_AccountExperiment

variable {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program) (a : Adversary A)

def firstSyntax (i : FirstInputs A) :=
  GExq_InstalledWrapper.first c.adapter c.currentBase c.stageBase c.finish
    c.reserved c.query c.geometry c.boundaries c.std hashv copy allocator i.entry id i.data i.state

def secondSyntax (i : SecondInputs A) :=
  GExq_InstalledWrapper.second c.adapter c.currentBase c.stageBase c.finish
    c.reserved c.query c.geometry c.boundaries c.std hashv allocator i.entry id i.data i.slot i.state

/-- Partial native-source evaluation, retaining the actual wrapper Results.
Only successful calls enter readLog; attempted cost is separately retained. -/
def run (native : Bytes → State) : List (Bytes × State) × Outcome A :=
  let i := eval native a.first
  let f := SdkC_Source.run hashv (firstSyntax c hashv copy allocator id i.2) []
  match f.1 with
  | .ok (.Ok (saved,post,final)) =>
    let j := eval native (a.second i.2 saved post final)
    let s := SdkC_Source.run hashv (secondSyntax c hashv allocator id j.2) []
    (i.1 ++ (SdkC_Source.readLog f.2 ++ (j.1 ++ SdkC_Source.readLog s.2)),
      (i.2,f.1,some (j.2,s.1)))
  | _ => (i.1 ++ SdkC_Source.readLog f.2,(i.2,f.1,none))

def attempts (native : Bytes → State) : Nat :=
  let i := eval native a.first
  let f := SdkC_Source.run hashv (firstSyntax c hashv copy allocator id i.2) []
  match f.1 with
  | .ok (.Ok (saved,post,final)) =>
    let j := eval native (a.second i.2 saved post final)
    let s := SdkC_Source.run hashv (secondSyntax c hashv allocator id j.2) []
    i.1.length + (f.2.length + (j.1.length + s.2.length))
  | _ => i.1.length + f.2.length

/-- An explicit reached-path certificate, not new runtime trust. It covers
pure wrapper failures as well as acceptance; a failed syscall is excluded. -/
def Certificate (native H : Bytes → State) : Prop :=
  ARS_AccountReplay.Consistent a.first native H ∧
  ARR_OracleCoverage.Covered H hashv
    (firstSyntax c hashv copy allocator id (eval native a.first).2) ∧
  (∀ saved post final,
    (SdkC_Source.run hashv (firstSyntax c hashv copy allocator id (eval native a.first).2) []).1 =
      ok (.Ok (saved,post,final)) →
    ARS_AccountReplay.Consistent (a.second (eval native a.first).2 saved post final) native H ∧
    ARR_OracleCoverage.Covered H hashv (secondSyntax c hashv allocator id
      (eval native (a.second (eval native a.first).2 saved post final)).2))

/-- Exact full-account representation on the certified native class. No bank
support or security bound is assumed or concluded by this source theorem. -/
theorem exact (native H : Bytes → State)
    (certificate : Certificate c hashv copy allocator id a native H) :
    eval H (account c hashv copy allocator id a) = run c hashv copy allocator id a native := by
  obtain ⟨prefixAgrees,firstCovered,secondCovered⟩ := certificate
  have firstChoice := ARS_AccountReplay.replay a.first native H prefixAgrees
  obtain ⟨firstResult,firstLog,_⟩ := ARR_OracleCoverage.exact H hashv
    (firstSyntax c hashv copy allocator id (eval native a.first).2) firstCovered []
  simp only [SdkC_Source.readLog,List.filterMap_nil,List.nil_append] at firstLog
  have firstSame : eval H (SCE_Execution.firstCode c hashv copy allocator id (eval native a.first).2) =
      (SdkC_Source.readLog (SdkC_Source.run hashv
        (firstSyntax c hashv copy allocator id (eval native a.first).2) []).2,
       (SdkC_Source.run hashv (firstSyntax c hashv copy allocator id (eval native a.first).2) []).1) :=
    Prod.ext firstLog.symm firstResult.symm
  rw [SCE_Execution.account_def]
  simp only [eval_bind,firstChoice,firstSame]
  unfold run
  dsimp only
  cases reply : (SdkC_Source.run hashv (firstSyntax c hashv copy allocator id (eval native a.first).2) []).1 with
  | fail error => simp only [reply,eval,List.append_nil]
  | div => simp only [reply,eval,List.append_nil]
  | ok result =>
    cases result with
    | Err error => simp only [reply,eval,List.append_nil]
    | Ok value =>
      rcases value with ⟨saved,post,final⟩
      obtain ⟨choice,covered⟩ := secondCovered saved post final reply
      have choiceSame := ARS_AccountReplay.replay _ native H choice
      obtain ⟨out,reads,_⟩ := ARR_OracleCoverage.exact H hashv
        (secondSyntax c hashv allocator id (eval native (a.second (eval native a.first).2 saved post final)).2) covered []
      simp only [SdkC_Source.readLog,List.filterMap_nil,List.nil_append] at reads
      have secondSame : eval H (SCE_Execution.secondCode c hashv allocator id
          (eval native (a.second (eval native a.first).2 saved post final)).2) =
          (SdkC_Source.readLog (SdkC_Source.run hashv (secondSyntax c hashv allocator id
            (eval native (a.second (eval native a.first).2 saved post final)).2) []).2,
          (SdkC_Source.run hashv (secondSyntax c hashv allocator id
            (eval native (a.second (eval native a.first).2 saved post final)).2) []).1) :=
        Prod.ext reads.symm out.symm
      simp only [reply,eval_bind,choiceSame,secondSame,eval,List.append_nil]

#print axioms exact
end AspisR1.ARS_NativeAccount
end
