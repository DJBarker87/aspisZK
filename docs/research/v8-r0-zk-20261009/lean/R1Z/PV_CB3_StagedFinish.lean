import R1Z.PV_CB3_StagedZero
import R1Z.PV_CB3_StagedMachineCarry
import R1Z.PV_CB3_MachineFinish
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB3_StagedFinish
open Aeneas Aeneas.Std
open PV_CB3_StagedPacking

def finish (digits : Array U32 8#usize) (high : U32) : Array U32 8#usize :=
  let first := PV_CB3_StagedMachineCarry.carry digits (U32.wrapping_add high 1#u32)
  if first.2 then (PV_CB3_StagedMachineCarry.carry first.1 1#u32).1 else first.1

theorem carry_bits (digits : Array U32 8#usize) (a : U32) :
    bits (PV_CB3_StagedMachineCarry.carry digits a).1 =
      (PV_CB3_MachineCarry.carry (bits digits) a.bv).1 := by
  simp only [PV_CB3_StagedMachineCarry.carry,bits_pack]

theorem neq_zero (v : BitVec 32) : ((⟨v⟩ : U32) != 0#u32) = decide (v ≠ 0) := by
  exact PV_CB3_StagedZero.neq_zero v

theorem overflow (digits : Array U32 8#usize) (a : U32) :
    (PV_CB3_StagedMachineCarry.carry digits a).2 =
      decide ((PV_CB3_MachineCarry.carry (bits digits) a.bv).2 ≠ 0) :=
  neq_zero _

theorem increment (high : U32) : (U32.wrapping_add high 1#u32).bv = high.bv + 1 := by rfl

theorem projection (digits : Array U32 8#usize) (high : U32) :
    bits (finish digits high) = PV_CB3_MachineFinish.finish (bits digits) high.bv := by
  by_cases h : (PV_CB3_MachineCarry.carry (bits digits) (high.bv + 1#32)).2 = 0#32
  · simp [finish,PV_CB3_MachineFinish.finish,overflow,carry_bits,increment,h]
  · simp [finish,PV_CB3_MachineFinish.finish,overflow,carry_bits,increment,h]
#print axioms carry_bits
#print axioms neq_zero
#print axioms overflow
#print axioms increment
#print axioms projection
end R1Z.PV_CB3_StagedFinish
