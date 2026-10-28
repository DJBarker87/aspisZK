import Aeneas.Std
namespace PV_B3P_Repeat226
open Aeneas Aeneas.Std
set_option autoImplicit false

theorem index_value {α : Type} {n : Usize} (a : Array α n) (i : Usize)
    (h : i.val < n.val) :
    Array.index_usize a i = .ok (a.val[i.val]'(by simpa [a.property] using h)) := by
  have hi : i.val < a.val.length := by simpa [a.property] using h
  unfold Array.index_usize
  change (match a.val[i.val]? with
    | none => Result.fail Error.arrayOutOfBounds
    | some x => Result.ok x) = Result.ok (a.val[i.val]'hi)
  rw [List.getElem?_eq_getElem hi]

theorem repeat_index {α : Type} (n : Usize) (x : α) (i : Usize)
    (h : i.val < n.val) : Array.index_usize (Array.repeat n x) i = .ok x := by
  rw [index_value _ _ h]
  simp only [Array.repeat_val, List.getElem_replicate]

theorem repeat_set {α : Type} (n : Usize) (x : α) (i : Usize)
    (h : i.val < n.val) : (Array.repeat n x).set i x = Array.repeat n x := by
  have hi : i.val < (Array.repeat n x).val.length := by simpa [Array.length_eq] using h
  have hx : (Array.repeat n x).val[i.val]'hi = x := by
    simp only [Array.repeat_val, List.getElem_replicate]
  calc
    (Array.repeat n x).set i x =
        (Array.repeat n x).set i ((Array.repeat n x).val[i.val]'hi) :=
      congrArg (fun value => (Array.repeat n x).set i value) hx.symm
    _ = Array.repeat n x := Array.set_getElem_eq _ _ hi

theorem repeat_update {α : Type} (n : Usize) (x : α) (i : Usize)
    (h : i.val < n.val) : Array.update (Array.repeat n x) i x = .ok (Array.repeat n x) := by
  have hi : i.val < (Array.repeat n x).val.length := by simpa [Array.length_eq] using h
  obtain ⟨b, hb, hval⟩ := WP.spec_imp_exists (Array.update_spec (Array.repeat n x) i x hi)
  rw [hval, repeat_set n x i h] at hb
  exact hb

theorem repeat_borrow {α : Type} (n : Usize) (x : α) (i : Usize)
    (h : i.val < n.val) : Array.index_mut_usize (Array.repeat n x) i =
      .ok (x, Aeneas.Std.Array.set (Array.repeat n x) i) := by
  simp only [Array.index_mut_usize, repeat_index n x i h, bind_tc_ok]

#print axioms index_value
#print axioms repeat_index
#print axioms repeat_set
#print axioms repeat_update
#print axioms repeat_borrow
end PV_B3P_Repeat226
