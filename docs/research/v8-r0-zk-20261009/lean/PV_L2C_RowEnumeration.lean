import PV_L2C_OwnedBalance
set_option autoImplicit false
namespace PV_L2C_RowEnumeration
open Aeneas Aeneas.Std Result PV_L2C_VecRead
open R1Z.ProverCommitBalanceRecursion PV_L2C_OwnedBalance

def index (i : Fin 1024) : Usize := Usize.ofNatCore i.val (by have := i.isLt; have := bound1024; omega)

theorem index_val (i : Fin 1024) : (index i).val=i.val := by rfl
#print axioms index_val

/-- Symbolic range equality, without normalizing the 1024-cell recurrence. -/
theorem enumeration : rows=List.ofFn index := by
  apply (List.map_inj_right (f:=fun r : Usize => r.val)
    (fun a b h => UScalar.eq_of_val_eq h)).mp
  rw [rows,sequence_ascending 1024 0#usize (by decide),List.map_ofFn]
  apply List.ext_getElem
  · simp only [List.length_range',List.length_ofFn]
  · intro i hi hj
    have hz : (0#usize).val=0 := by scalar_tac
    simp only [List.getElem_range',List.getElem_ofFn,Function.comp_apply,index_val,hz,
      Nat.mul_one,Nat.one_mul,Nat.zero_add]
#print axioms enumeration
end PV_L2C_RowEnumeration
