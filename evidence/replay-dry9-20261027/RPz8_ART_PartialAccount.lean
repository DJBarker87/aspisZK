import RPz8_ART_PartialExact
import RPz8_ARS_NativeOutcome
set_option autoImplicit false
noncomputable section
namespace AspisR1.ART_PartialAccount
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open GExq_AccountExperiment SCE_Experiment ARS_NativeAccount

/-- A failure-aware observer of the SAME literal source syntax. Hash failure
stops before the continuation, but its issued address is still charged. -/
def wrapper {V : Type} (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (code : SdkC_Source.Code V) : Program Bytes State (Result V) :=
  bind (ART_PartialProgram.program hashv code []) (fun raw => .done raw.1)

variable {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program) (a : Adversary A)

def account : Program Bytes State (Outcome A) :=
  bind a.first fun i =>
    bind (wrapper hashv (firstSyntax c hashv copy allocator id i)) fun reply =>
      match reply with
      | .ok (.Ok (saved,post,final)) =>
        bind (a.second i saved post final) fun j =>
          bind (wrapper hashv (secondSyntax c hashv allocator id j)) fun out =>
            .done (i,reply,some (j,out))
      | _ => .done (i,reply,none)

/-- Native successes and rejections have the same certificate: agreement at
returned calls, original first choice, and only the actually reached TX2 choice.
This is a derived coverage criterion, not an extra top security premise. -/
def Certificate (native H : Bytes → State) : Prop :=
  ARS_AccountReplay.Consistent a.first native H ∧
  ARS_QueryTransport.Agrees H
    (SdkC_Source.run hashv (firstSyntax c hashv copy allocator id (eval native a.first).2) []).2 ∧
  (∀ saved post final,
    (SdkC_Source.run hashv (firstSyntax c hashv copy allocator id (eval native a.first).2) []).1 =
      ok (.Ok (saved,post,final)) →
    ARS_AccountReplay.Consistent (a.second (eval native a.first).2 saved post final) native H ∧
    ARS_QueryTransport.Agrees H (SdkC_Source.run hashv (secondSyntax c hashv allocator id
      (eval native (a.second (eval native a.first).2 saved post final)).2) []).2)

/-- Charge-log representation, with the actual native Outcome. Failed syscall
answers in the bookkeeping log are ghosts and never enter that Outcome. -/
def represented (native H : Bytes → State) : List (Bytes × State) × Outcome A :=
  let i := eval native a.first
  let f := SdkC_Source.run hashv (firstSyntax c hashv copy allocator id i.2) []
  match f.1 with
  | .ok (.Ok (saved,post,final)) =>
    let j := eval native (a.second i.2 saved post final)
    let s := SdkC_Source.run hashv (secondSyntax c hashv allocator id j.2) []
    (i.1 ++ (ART_PartialProgram.attempted H f.2 ++
      (j.1 ++ ART_PartialProgram.attempted H s.2)),(i.2,f.1,some (j.2,s.1)))
  | _ => (i.1 ++ ART_PartialProgram.attempted H f.2,(i.2,f.1,none))

end AspisR1.ART_PartialAccount
end
