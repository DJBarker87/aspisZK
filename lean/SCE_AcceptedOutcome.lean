import SCE_Execution
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCE_AcceptedOutcome
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open GExq_AccountExperiment SCE_Experiment SCE_Execution
variable {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)
    (a : Adversary A) (H : Bytes → State)

theorem from_source_calls
    (saved : alloc.vec.Vec U8) (post post2 : Heap (Nat → Record)) (final final2 : A)
    (first : (eval H (firstCode c hashv copy allocator id (eval H a.first).2)).2 =
      .ok (.Ok (saved,post,final)))
    (second : (eval H (secondCode c hashv allocator id
      (eval H (a.second (eval H a.first).2 saved post final)).2)).2 = .ok (.Ok (post2,final2))) :
    accepted (eval H (account c hashv copy allocator id a)).2 = true := by
  rw [accepted_eval c hashv copy allocator id a H saved post final first]
  dsimp only
  rw [first,second]
  rfl

theorem runtime_acceptance
    (run : F3T_Experiment.RunView)
    (observed : (eval H (runtime c hashv copy allocator id a)).2 = some run) :
    run.2.2 = accepted (eval H (account c hashv copy allocator id a)).2 := by
  rw [runtime_eval] at observed
  exact (congrArg (fun v : F3T_Experiment.RunView => v.2.2) (Option.some.inj observed)).symm

#print axioms from_source_calls
#print axioms runtime_acceptance
end AspisR1.SCE_AcceptedOutcome
end
