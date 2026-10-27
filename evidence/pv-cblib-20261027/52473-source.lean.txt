import R1Z.PV_CBL_ArrayReadValue
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_ArrayMutableValue
set_option autoImplicit false
theorem read_write {T : Type} [Inhabited T] {N : Usize} (a : Array T N) (i : Usize)
    (h : i.val<N.val) :
    Array.index_mut_usize a i = ok (a.val[i.val]!,fun x => a.set i x) := by
  unfold Array.index_mut_usize
  rw [PV_CBL_ArrayReadValue.read a i h,bind_tc_ok]
#print axioms read_write
end R1Z.PV_CBL_ArrayMutableValue
