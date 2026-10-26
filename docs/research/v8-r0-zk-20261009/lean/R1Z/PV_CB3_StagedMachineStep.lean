import R1Z.PV_CB3_StagedSource
import R1Z.PV_CB3_MachineCarryStep
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB3_StagedMachineStep
open Aeneas Aeneas.Std Result
/-- Exact typed Result at the scalar word site; no range premise. -/
theorem word (w : U32) (r : U64) :
    PV_CB3_StagedSource.staged_reference.word_step w r =
      ok (⟨(PV_CB3_WordMachine.step w.bv r.bv).1⟩,
          ⟨(PV_CB3_WordMachine.step w.bv r.bv).2⟩) := by
  rfl
/-- Exact carry step, including both narrowing casts, over all raw words. -/
theorem carry (d a : U32) :
    PV_CB3_StagedSource.staged_reference.carry_step d a =
      ok (⟨(PV_CB3_MachineCarryStep.step d.bv a.bv).1⟩,
          ⟨(PV_CB3_MachineCarryStep.step d.bv a.bv).2⟩) := by
  rfl
/-- The compatibility adjustment changes only the scalar literal carrier. -/
theorem shift_literal : (32#i32).val = ((32#u32).val : Int) := rfl
#print axioms word
#print axioms carry
#print axioms shift_literal
end R1Z.PV_CB3_StagedMachineStep
