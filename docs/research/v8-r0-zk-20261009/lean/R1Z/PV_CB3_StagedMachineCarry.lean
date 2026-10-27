import R1Z.PV_CB3_StagedMachineStep
import R1Z.PV_CB3_StagedPacking
import R1Z.PV_CB3_ArrayEight
import R1Z.PV_CB3_MachineCarry
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB3_StagedMachineCarry
open Aeneas Aeneas.Std Result
open PV_CB3_StagedPacking

def carry (digits : Array U32 8#usize) (a : U32) : Array U32 8#usize × Bool :=
  (pack (PV_CB3_MachineCarry.carry (bits digits) a.bv).1
    (by rw [PV_CB3_MachineCarry.length_preserved,bits_length]),
   (⟨(PV_CB3_MachineCarry.carry (bits digits) a.bv).2⟩ : U32) != 0#u32)

/-- Exact carrier and overflow test, over arbitrary raw digit words. -/
theorem source (digits : Array U32 8#usize) (a : U32) :
    PV_CB3_StagedSource.staged_reference.carry digits a = ok (carry digits a) := by
  obtain ⟨a0,b,c,d,e,f,g,h,hview⟩ := PV_CB3_ArrayEight.view digits
  subst digits
  simp [carry,PV_CB3_StagedSource.staged_reference.carry,
    PV_CB3_StagedMachineStep.carry,PV_CB3_MachineCarry.carry,
    bits,pack,Array.make,Array.index_usize,lift,bind_tc_ok]
#print axioms source
end R1Z.PV_CB3_StagedMachineCarry
