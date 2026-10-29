import R1Z.PV_RDB2F_Low
namespace R1Z.PV_RDB2F_InitialFromFn
open Aeneas Aeneas.Std Result
set_option autoImplicit false
/-- The exact first from_fn slice has length four and stays inside block32. -/
theorem slice_bounds (i : Nat) (h : i<8) :
    4*i≤4*i+4 ∧ 4*i+4≤32 ∧ (4*i+4)-(4*i)=4 := by omega

theorem slice_length (block : Array U8 32#usize) (i : Nat) (h : i<8) :
    ((block.val.drop (4*i)).take 4).length=4 := by
  simp only [List.length_take,List.length_drop,block.property]
  change min 4 (32-4*i)=4
  omega

#print axioms slice_bounds
#print axioms slice_length
end R1Z.PV_RDB2F_InitialFromFn
