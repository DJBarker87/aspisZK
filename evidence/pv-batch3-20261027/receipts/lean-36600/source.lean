import Aeneas.Std
namespace PV_B3_SparseArray
open Aeneas Aeneas.Std Result
set_option autoImplicit false
variable {A : Type}

-- The state is a function of the queried endpoint. No 1024-cell recurrence
-- is evaluated to read or update one endpoint.
def array (size : Usize) (xs : Nat → A) : Array A size :=
  ⟨List.ofFn (fun i : Fin size.val => xs i.val), by simp only [List.length_ofFn]⟩

theorem index (size : Usize) (xs : Nat → A) (i : Usize) (hi : i.val < size.val) :
    Array.index_usize (array size xs) i = ok (xs i.val) := by
  have hidx : i.val < (array size xs).val.length := by
    simp only [array, List.length_ofFn]; exact hi
  unfold Array.index_usize
  change (match (array size xs).val[i.val]? with
    | none => Result.fail Error.arrayOutOfBounds
    | some x => Result.ok x) = Result.ok (xs i.val)
  rw [List.getElem?_eq_getElem hidx]
  simp only [array, List.getElem_ofFn]

theorem update (size : Usize) (xs : Nat → A) (i : Usize)
    (hi : i.val < size.val) (z : A) :
    Array.update (array size xs) i z =
      ok (array size (Function.update xs i.val z)) := by
  have hidx : i.val < (array size xs).val.length := by
    simp only [array, List.length_ofFn]; exact hi
  obtain ⟨out, hout, hset⟩ := WP.spec_imp_exists
    (Array.update_spec (array size xs) i z hidx)
  rw [hout]
  apply congrArg Result.ok
  rw [hset]
  apply Subtype.ext
  change (array size xs).val.set i.val z =
    (array size (Function.update xs i.val z)).val
  apply List.ext_getElem
  · simp only [List.length_set, array, List.length_ofFn]
  · intro k hk1 hk2
    simp only [array, List.getElem_set, List.getElem_ofFn]
    by_cases h : k = i.val
    · subst k; simp only [Function.update_self, if_true]
    · simp only [Ne.symm h, if_false, Function.update_of_ne h]

theorem constant (size : Usize) (x : A) :
    array size (fun _ => x) = Array.repeat size x := by
  apply Subtype.ext
  apply List.ext_getElem
  · simp only [array, List.length_ofFn, Array.repeat, List.length_replicate]
  · intro k hk1 hk2
    simp only [array, List.getElem_ofFn, Array.repeat, List.getElem_replicate]

#print axioms array
#print axioms index
#print axioms update
#print axioms constant
end PV_B3_SparseArray
