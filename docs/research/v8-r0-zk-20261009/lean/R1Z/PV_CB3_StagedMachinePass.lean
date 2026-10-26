import R1Z.PV_CB3_StagedCast
import R1Z.PV_CB3_StagedMachineStep
import R1Z.PV_CB3_StagedPacking
import R1Z.PV_CB3_ArrayEight
import R1Z.PV_CB3_MachinePass
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB3_StagedMachinePass
open Aeneas Aeneas.Std Result
open PV_CB3_StagedPacking

def pass (rank : Array U32 8#usize) : Array U32 8#usize × U32 :=
  (pack (PV_CB3_MachinePass.passLE (bits rank)).1
    (by rw [PV_CB3_MachinePass.length_preserved,bits_length]),
   ⟨(PV_CB3_MachinePass.passLE (bits rank)).2.setWidth 32⟩)

/-- The complete extracted pass equals the typed machine recurrence. -/
theorem source (rank : Array U32 8#usize) :
    PV_CB3_StagedSource.staged_reference.pass rank = ok (pass rank) := by
  obtain ⟨a,b,c,d,e,f,g,h,hview⟩ := PV_CB3_ArrayEight.view rank
  subst rank
  simp [pass,PV_CB3_StagedSource.staged_reference.pass,
    PV_CB3_StagedMachineStep.word,PV_CB3_MachinePass.passLE,
    PV_CB3_StagedCast.narrow,bits,pack,Array.make,Array.index_usize,lift,bind_tc_ok]
#print axioms source
end R1Z.PV_CB3_StagedMachinePass
