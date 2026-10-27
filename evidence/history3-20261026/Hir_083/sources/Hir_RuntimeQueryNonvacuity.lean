import Hir_RuntimeNonvacuity
import Hir_WriterCharge
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hir_RuntimeQueryNonvacuity
open Aeneas Aeneas.Std Result Hist_Store Hist_RuntimeEntry
open S2Trust S2W_D189Entry S2W_D189Wrappers Hir_Call Hir_Schedule Hir_RuntimeNonvacuity
open Hist_Nonvacuity (key different)
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

theorem source {F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (native1 : S2W_ExtractionBoundary.First)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator Unit) (H : Bytes → State) :
    eval H (Hir_Schedule.program native1 copy allocator (key 0#u8) c hashv initial schedule) =
      ([([],H [])],(Hist_Store.put initial 0 created,
        [.committedWrite 0 (MultiproofConeCanonical.bytesOf zeros.val),.rollback],())) := by
  have authorized : key 1#u8 ≠ key 0#u8 ∧ (initial 0).owner = key 1#u8 := ⟨different,rfl⟩
  simp only [schedule,Hir_Schedule.program,eval,eval_bind,Hiq_NativeAction.apply,if_pos authorized,created,
    List.nil_append,List.append_nil]

#print axioms source
end AspisR1.Hir_RuntimeQueryNonvacuity
end
