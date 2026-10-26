import SCE_Execution
import SCE_Projection
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCE_AdaptivePadding
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open GExq_AccountExperiment SCE_Experiment SCE_Execution

/-- A permitted adaptive adversary may make one extra oracle request before
returning exactly the same second submission. The response is deliberately
ignored. This changes issued chronology, not the native wrapper inputs. -/
def pad {A : Type} (a : Adversary A) (address : Bytes) : Adversary A :=
  {a with second := fun i saved post final => .ask address (fun _ => a.second i saved post final)}

theorem submission_same {A : Type} (a : Adversary A) (address : Bytes) :
    submission (pad a address) = submission a := rfl

theorem choice_eval {A : Type} (a : Adversary A) (address : Bytes)
    (i : FirstInputs A) (saved : alloc.vec.Vec U8) (post : Heap (Nat → Record))
    (final : A) (H : Bytes → State) :
    eval H ((pad a address).second i saved post final) =
      ((address,H address) :: (eval H (a.second i saved post final)).1,
        (eval H (a.second i saved post final)).2) := rfl

variable {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)
    (a : Adversary A) (address : Bytes) (H : Bytes → State)
    (saved : alloc.vec.Vec U8) (post : Heap (Nat → Record)) (final : A)
    (first : (eval H (firstCode c hashv copy allocator id (eval H a.first).2)).2 =
      .ok (.Ok (saved,post,final)))

include first

theorem outcome_same :
    (eval H (account c hashv copy allocator id (pad a address))).2 =
      (eval H (account c hashv copy allocator id a)).2 := by
  rw [accepted_eval c hashv copy allocator id (pad a address) H saved post final first,
    accepted_eval c hashv copy allocator id a H saved post final first]
  rfl

/-- Even with a SINGLE shared adversary construction, exact chronology can
change while the headline submission and complete terminal account outcome
stay identical. This is not a forgery or an assertion of source acceptance. -/
theorem log_length :
    (eval H (account c hashv copy allocator id (pad a address))).1.length =
      (eval H (account c hashv copy allocator id a)).1.length + 1 := by
  rw [accepted_eval c hashv copy allocator id (pad a address) H saved post final first,
    accepted_eval c hashv copy allocator id a H saved post final first]
  simp only [pad,eval,List.length_append,List.length_cons]
  omega

#print axioms submission_same
#print axioms choice_eval
#print axioms outcome_same
#print axioms log_length
end AspisR1.SCE_AdaptivePadding
end
