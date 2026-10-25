import Hir_SyscallStatusGap
import Hist_Nonvacuity
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hir_RuntimeNonvacuity
open Aeneas Aeneas.Std Result Hist_Store Hist_RuntimeEntry
open S2Trust S2W_D189Entry S2W_D189Wrappers Hir_Call Hir_Schedule Hir_ProvenanceModel
open Hist_Nonvacuity (key different)
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

def zeros : Slice U8 := ⟨List.replicate 1768 0#u8,by simp only [List.length_replicate]; scalar_tac⟩
def initial : Store := fun _ => ⟨key 1#u8,zeros⟩
def created : Cell := ⟨key 0#u8,zeros⟩
def schedule : Schedule Unit Unit :=
  .ask [] (fun _ => .foreign (key 1#u8) 0 created (fun _ => .rollback (.done ())))

theorem genesis : ∀ address, (initial address).owner = key 0#u8 → ¬ Initialized (initial address).data := by
  intro address owner
  exact False.elim (different owner)

theorem zero : Zero zeros := by
  intro byte member
  exact List.eq_of_mem_replicate member

theorem reached (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator Unit) (H : Bytes → State) :
    run native1 native2 copy allocator (key 0#u8) H initial schedule =
      (put initial 0 created,[.committedWrite 0 (MultiproofConeCanonical.bytesOf zeros.val),.rollback],()) := by
  have authorized : key 1#u8 ≠ key 0#u8 ∧ (initial 0).owner = key 1#u8 := ⟨different,rfl⟩
  simp only [schedule,run,Hiq_NativeAction.apply,if_pos authorized,created]

theorem admissibility (native1 : S2W_ExtractionBoundary.First) (native2 : S2W_ExtractionBoundary.Second)
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator Unit) (H : Bytes → State) :
    admissible native1 native2 copy allocator (key 0#u8) H initial schedule := by
  change (_ ∨ Assignable initial 0 created) ∧ True
  exact ⟨Or.inr (Or.inr zero),True.intro⟩

#print axioms genesis
#print axioms zero
#print axioms reached
#print axioms admissibility
end AspisR1.Hir_RuntimeNonvacuity
end
