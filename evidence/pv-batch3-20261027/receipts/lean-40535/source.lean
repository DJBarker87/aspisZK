import PV_B3_ZeroArithmetic
import PV_B3_SparseSet
namespace PV_B3_ZeroArrays
open Aeneas Aeneas.Std Result PV_B3_ZeroArithmetic
set_option autoImplicit false

theorem triple_repeat {A : Type} (x : A) : Array.make 3#usize [x,x,x] = Array.repeat 3#usize x := rfl

theorem mutable_repeat {A : Type} (n : Usize) (x : A) (i : Usize) (hi : i.val < n.val) :
    Array.index_mut_usize (Array.repeat n x) i =
      ok (x, fun z => Aeneas.Std.Array.set (Array.repeat n x) i z) := by
  unfold Array.index_mut_usize
  rw [index_repeat n x i hi]
  rfl

theorem set_repeat {A : Type} (n : Usize) (x : A) (i : Usize) :
    Aeneas.Std.Array.set (Array.repeat n x) i x = Array.repeat n x := by
  rw [← PV_B3_SparseArray.constant,PV_B3_SparseSet.set]
  have he : Function.update (fun _ : Nat => x) i.val x = (fun _ : Nat => x) := by
    funext k
    by_cases hk : k = i.val
    · subst k; rw [Function.update_self]
    · rw [Function.update_of_ne hk]
  rw [he]

#print axioms triple_repeat
#print axioms mutable_repeat
#print axioms set_repeat
end PV_B3_ZeroArrays
