import CPP_Protection
import Hist_Nonvacuity
set_option autoImplicit false
noncomputable section
namespace AspisR1.CPP_Nonvacuity
open Aeneas Aeneas.Std Result Hist_Store Hist_RuntimeEntry
open S2Trust S2W_D189Entry S2W_D189Wrappers Hir_Call CPP_Invocation CPP_Oracle CPP_Schedule
open Hist_Nonvacuity (key different original changed initialized)
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
attribute [local instance] Classical.propDecidable

def data : Slice U8 := ⟨[3#u8,10#u8],by simp only [List.length_cons,List.length_nil]; scalar_tac⟩
def input (layout : Layout) : Invocation Unit := ⟨⟨layout,data,.Ok 0#u64,()⟩,0⟩
def schedule (layout : Layout) : CPP_Schedule.Schedule Unit Unit :=
  .ask [] (fun _ => .invoke (input layout) (fun _ =>
    .foreign (key 1#u8) 1 changed (fun _ => .rollback (.done ()))))

theorem route : Hiq_ReleaseRoute.route data = .first :=
  (Hiq_ReleaseRoute.first_iff data).mpr (Or.inl rfl)

theorem incompatible (layout : Layout) : ¬ compatible (input layout) := by
  simp only [compatible,input,route]
  decide

/-- A nonempty trace has a rejected count0 TX1, an actual authorized foreign
write and rollback, preceded by an oracle query. No native child is assumed
successful, and arbitrary native children/allocators cannot affect this run. -/
theorem reached (n1 : S2W_ExtractionBoundary.First) (n2 : S2W_ExtractionBoundary.Second)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator Unit) (layout : Layout) (H : Bytes → State) :
    CPP_Schedule.run n1 n2 copy allocator (key 0#u8) H original (schedule layout) =
      (put original 1 changed,[.rollback,.committedWrite 1 (MultiproofConeCanonical.bytesOf changed.data.val),.rollback],()) := by
  have owner : (original 1).owner = key 1#u8 := by simp only [original,show (1:Nat) ≠ 0 by decide,if_false]
  simp only [schedule,CPP_Schedule.run,
    CPP_Compatibility.invalid n1 n2 copy allocator (key 0#u8) original (input layout) (incompatible layout),
    Hiq_NativeAction.apply,if_pos (And.intro different owner)]

#print axioms route
#print axioms incompatible
#print axioms reached
end AspisR1.CPP_Nonvacuity
end
