import PV_B3_ArrayCarrier
namespace PV_B3_ArrayUpdateCarrier
open Aeneas Aeneas.Std Result PV_B3_ArrayCarrier
set_option autoImplicit false

theorem update_eq_set {A : Type} {n : Usize} (a : Array A n) (i : Usize) (x : A)
    (hi : i.val < n.val) : Array.update a i x = ok (Aeneas.Std.Array.set a i x) := by
  have hidx : i.val < a.val.length := by rw [a.property]; exact hi
  obtain ⟨out, hout, hset⟩ := WP.spec_imp_exists (Array.update_spec a i x hidx)
  rw [hset] at hout
  exact hout

theorem update_outside {A : Type} {n : Usize} (a : Array A n) (i : Usize) (x : A)
    (hi : n.val ≤ i.val) : Array.update a i x = fail Error.arrayOutOfBounds := by
  have hn : a.val[i.val]? = none := List.getElem?_eq_none (by rw [a.property]; exact hi)
  unfold Array.update
  change (match a.val[i.val]? with
    | none => Result.fail Error.arrayOutOfBounds
    | some _ => Result.ok (Aeneas.Std.Array.set a i x)) = _
  rw [hn]

theorem update {A B : Type} {n : Usize} (f : A → B) (a : Array A n) (i : Usize) (x : A) :
    resultMap (arrayMap f) (Array.update a i x) = Array.update (arrayMap f a) i (f x) := by
  by_cases hi : i.val < n.val
  · rw [update_eq_set a i x hi, update_eq_set (arrayMap f a) i (f x) hi]
    change ok (arrayMap f (Aeneas.Std.Array.set a i x)) = _
    rw [PV_B3_ArrayCarrier.set]
  · have hn : n.val ≤ i.val := Nat.le_of_not_gt hi
    rw [update_outside a i x hn, update_outside (arrayMap f a) i (f x) hn]
    rfl

#print axioms update_eq_set
#print axioms update_outside
#print axioms update
end PV_B3_ArrayUpdateCarrier
