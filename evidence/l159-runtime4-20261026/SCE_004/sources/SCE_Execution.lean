import SCE_Experiment
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCE_Execution
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open GExq_AccountExperiment SCE_Experiment
variable {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)

def firstCode (i : FirstInputs A) :=
  SdkC_Oracle.program (GExq_InstalledWrapper.first c.adapter c.currentBase c.stageBase c.finish
    c.reserved c.query c.geometry c.boundaries c.std hashv copy allocator i.entry id i.data i.state)

def secondCode (i : SecondInputs A) :=
  SdkC_Oracle.program (GExq_InstalledWrapper.second c.adapter c.currentBase c.stageBase c.finish
    c.reserved c.query c.geometry c.boundaries c.std hashv allocator i.entry id i.data i.slot i.state)

theorem account_def (a : Adversary A) :
    account c hashv copy allocator id a =
      bind a.first fun i =>
        bind (firstCode c hashv copy allocator id i) fun reply =>
          match reply with
          | .ok (.Ok (saved,post,final)) =>
            bind (a.second i saved post final) fun next =>
              bind (secondCode c hashv allocator id next) fun out => .done (i,reply,some (next,out))
          | _ => .done (i,reply,none) := rfl

/-- Successful branches retain exactly prefix, first wrapper, adaptive
choice, and second wrapper in that chronological order. -/
theorem accepted_eval (a : Adversary A) (H : Bytes → State)
    (saved : alloc.vec.Vec U8) (post : Heap (Nat → Record)) (final : A)
    (first : (eval H (firstCode c hashv copy allocator id (eval H a.first).2)).2 =
      .ok (.Ok (saved,post,final))) :
    let i := eval H a.first
    let f := eval H (firstCode c hashv copy allocator id i.2)
    let s := eval H (a.second i.2 saved post final)
    let t := eval H (secondCode c hashv allocator id s.2)
    eval H (account c hashv copy allocator id a) =
      (i.1 ++ (f.1 ++ (s.1 ++ t.1)),(i.2,f.2,some (s.2,t.2))) := by
  rw [account_def]
  simp only [eval_bind,first,eval,List.append_nil]

#print axioms account_def
#print axioms accepted_eval
end AspisR1.SCE_Execution
end
