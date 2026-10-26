import CPP_AtomicSource
import Hist_Nonvacuity
set_option autoImplicit false
noncomputable section
namespace AspisR1.CPP_AtomicNonvacuity
open Aeneas Aeneas.Std Result Hist_Store Hist_RuntimeEntry
open S2Trust S2W_D189Entry S2W_D189Wrappers
open Hist_Nonvacuity (key different original changed)
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
attribute [local instance] Classical.propDecidable

def code : CPP_Schedule.Schedule Unit (CPP_Atomic.Reply Unit) :=
  .ask [] (fun _ => .foreign (key 1#u8) 1 changed (fun _ =>
    .done (.ok (.Err .InvalidInstructionData))))

theorem tentative (n1 : S2W_ExtractionBoundary.First) (n2 : S2W_ExtractionBoundary.Second)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator Unit) (H : Bytes → State) :
    CPP_Schedule.run n1 n2 copy allocator (key 0#u8) H original code =
      (Hist_Store.put original 1 changed,[.committedWrite 1 (MultiproofConeCanonical.bytesOf changed.data.val)],
        .ok (.Err .InvalidInstructionData)) := by
  have owner : (original 1).owner = key 1#u8 := by simp only [original,show (1:Nat) ≠ 0 by decide,if_false]
  simp only [code,CPP_Schedule.run,Hiq_NativeAction.apply,if_pos (And.intro different owner)]

theorem rollback (n1 : S2W_ExtractionBoundary.First) (n2 : S2W_ExtractionBoundary.Second)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator Unit) (H : Bytes → State) :
    CPP_Atomic.run n1 n2 copy allocator (key 0#u8) H original code =
      (original,[.rollback],.ok (.Err .InvalidInstructionData)) := by
  rw [CPP_Atomic.run,tentative]
  rfl

theorem queried {F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (n1 : S2W_ExtractionBoundary.First)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator Unit) (H : Bytes → State) :
    (eval H (CPP_Atomic.program n1 copy allocator (key 0#u8) c hashv original code)).1 = [([],H [])] := by
  have owner : (original 1).owner = key 1#u8 := by simp only [original,show (1:Nat) ≠ 0 by decide,if_false]
  simp only [CPP_AtomicSource.evaluation,code,CPP_Schedule.program,Hiq_NativeAction.apply,
    if_pos (And.intro different owner),eval,eval_bind,List.append_nil]

#print axioms tentative
#print axioms rollback
#print axioms queried
end AspisR1.CPP_AtomicNonvacuity
end
