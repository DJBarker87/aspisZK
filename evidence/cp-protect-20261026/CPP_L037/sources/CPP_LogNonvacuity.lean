import CPP_Nonvacuity
set_option autoImplicit false
noncomputable section
namespace AspisR1.CPP_LogNonvacuity
open Aeneas Aeneas.Std Result Hist_Store Hist_RuntimeEntry
open S2Trust S2W_D189Entry S2W_D189Wrappers Hir_Call CPP_Invocation CPP_Oracle CPP_Schedule
open Hist_Nonvacuity (key different original changed initialized)
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
attribute [local instance] Classical.propDecidable

theorem exact {F C : Type} (c : DrvC_Installation.Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (n1 : S2W_ExtractionBoundary.First)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator Unit) (layout : Layout) (H : Bytes → State) :
    eval H (CPP_Schedule.program n1 copy allocator (key 0#u8) c hashv original (CPP_Nonvacuity.schedule layout)) =
      ([([],H [])],(Hist_Store.put original 1 changed,
        [.rollback,.committedWrite 1 (MultiproofConeCanonical.bytesOf changed.data.val),.rollback],())) := by
  have owner : (original 1).owner = key 1#u8 := by simp only [original,show (1:Nat) ≠ 0 by decide,if_false]
  simp only [CPP_Nonvacuity.schedule,CPP_Schedule.program,CPP_Oracle.program,
    if_neg (CPP_Nonvacuity.incompatible layout),eval,eval_bind,
    Hiq_NativeAction.apply,if_pos (And.intro different owner),List.nil_append,List.append_nil]

#print axioms exact
end AspisR1.CPP_LogNonvacuity
end
