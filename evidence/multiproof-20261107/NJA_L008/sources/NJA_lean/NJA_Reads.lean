import NJA_Arity

set_option autoImplicit false
namespace NJA_Reads
open Aeneas Aeneas.Std Result NJA_Multiproof

theorem index_ok {α : Type} {n : Usize} (a : Array α n) (i : Usize)
    (hi : i.val < n.val) :
    Array.index_usize a i = ok (a.val[i.val]'(by simpa [a.property] using hi)) := by
  have h : i.val < a.val.length := by simpa [a.property] using hi
  unfold Array.index_usize
  change (match a.val[i.val]? with
    | none => Result.fail Error.arrayOutOfBounds
    | some x => Result.ok x) = Result.ok (a.val[i.val]'h)
  rw [List.getElem?_eq_getElem h]

theorem index_bad {α : Type} {n : Usize} (a : Array α n) (i : Usize)
    (hi : n.val ≤ i.val) :
    Array.index_usize a i = fail Error.arrayOutOfBounds := by
  unfold Array.index_usize
  have h : a.val.length ≤ i.val := by simpa [a.property] using hi
  change (match a.val[i.val]? with
    | none => Result.fail Error.arrayOutOfBounds
    | some x => Result.ok x) = Result.fail Error.arrayOutOfBounds
  rw [List.getElem?_eq_none h]

theorem root_result (values : Array (Array U8 32#usize) 16#usize)
    (root : Array U8 32#usize) :
    multiproof.root_matches values root =
      core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8
        (values.val[0]'(by simp [values.property])) root := by
  unfold multiproof.root_matches
  rw [index_ok values 0#usize (by scalar_tac)]
  rfl

#print axioms index_ok
#print axioms index_bad
#print axioms root_result
end NJA_Reads
