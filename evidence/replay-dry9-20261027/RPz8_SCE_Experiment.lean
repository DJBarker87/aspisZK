import RPz7_CPG_Account
import RPz8_SCD_Carrier
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCE_Experiment
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open F3T_Experiment F3T_ByteCarrier GExq_AccountExperiment

/-- One adversary, fixed before the oracle. The second submission is fully
response-driven; no successful result or selected trace is a field. -/
structure Adversary (A : Type) where
  first : Program Bytes State (FirstInputs A)
  second : FirstInputs A → alloc.vec.Vec U8 → Heap (Nat → Record) → A →
    Program Bytes State (SecondInputs A)

/-- The original first account buffers, not post-call allocation reads.
The verifier receives the 57607-byte suffix after the 688-byte Pool prefix. -/
def submitted {A : Type} (i : FirstInputs A) : Submission :=
  ⟨MultiproofConeCanonical.bytesOf (i.entry.buffers (i.entry.handles 1).1).val,
   (MultiproofConeCanonical.bytesOf (i.entry.buffers (i.entry.handles 0).1).val).drop 688⟩

def submission {A : Type} (a : Adversary A) : ByteProver :=
  bind a.first fun i => .done (submitted i)

def account {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program) (a : Adversary A) :=
  CPG_Account.source c hashv copy allocator id a.first a.second

/-- Acceptance is computed from BOTH actual wrapper results. Rejection is
retained with its attempted oracle log, rather than discarded. -/
def accepted {A : Type} (o : Outcome A) : Bool :=
  match o.2.1,o.2.2 with
  | .ok (.Ok _),some (_, .ok (.Ok _)) => true
  | _,_ => false

/-- A ghost observer of the actual account program. It performs no verifier
replay. Its returned log is exactly that program's chronological log. -/
def runtime {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program) (a : Adversary A) :
    F3T_Runtime.Runtime :=
  bind (OracleProgramRecording.record (account c hashv copy allocator id a)) fun v =>
    .done (some (v.1,(F3T_Canon.canonInput (input c (submitted v.2.1)),accepted v.2)))

theorem submission_eval {A : Type} (a : Adversary A) (H : Bytes → State) :
    eval H (submission a) = ((eval H a.first).1,submitted (eval H a.first).2) := by
  simp only [submission,eval_bind,eval,List.append_nil]

/-- Both terminal and rejecting account outcomes retain the original first
submission, independently of all source/crypto/runtime admission laws. -/
theorem first_projection {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)
    (a : Adversary A) (H : Bytes → State) :
    (eval H (account c hashv copy allocator id a)).2.1 = (eval H a.first).2 := by
  unfold account CPG_Account.source GExq_AccountExperiment.program
  simp only [eval_bind]
  split <;> simp only [eval_bind,eval]

theorem runtime_eval {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (id : S2W_ExtractionBoundary.Program)
    (a : Adversary A) (H : Bytes → State) :
    eval H (runtime c hashv copy allocator id a) =
      let v := eval H (account c hashv copy allocator id a)
      (v.1,some (v.1,(F3T_Canon.canonInput (input c (submitted v.2.1)),accepted v.2))) := by
  simp only [runtime,eval_bind,OracleProgramRecording.eval_record,eval,List.append_nil]

#print axioms submission_eval
#print axioms first_projection
#print axioms runtime_eval
end AspisR1.SCE_Experiment
end
