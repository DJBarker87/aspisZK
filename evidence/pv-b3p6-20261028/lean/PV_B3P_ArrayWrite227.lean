import PV_B3P_SelectIndex227
namespace PV_B3P_ArrayWrite227
open Aeneas Aeneas.Std PV_B3P_SelectIndex227
set_option autoImplicit false

theorem borrow {α : Type} {n : Usize} (xs : Array α n) (i : Usize)
    (hi : i.val<n.val) :
    Aeneas.Std.Array.index_mut_usize xs i =
      .ok (xs.val[i.val]'(by simpa only [xs.property] using hi),Aeneas.Std.Array.set xs i) := by
  unfold Aeneas.Std.Array.index_mut_usize
  rw [index_value xs i hi]
  rfl

theorem restore {α : Type} {n : Usize} (xs : Array α n) (i : Usize)
    (hi : i.val<n.val) (change : α → Result α) :
    (do
      let (old,back) ← Aeneas.Std.Array.index_mut_usize xs i
      let updated ← change old
      .ok (back updated)) = (do
      let updated ← change (xs.val[i.val]'(by simpa only [xs.property] using hi))
      .ok (Aeneas.Std.Array.set xs i updated)) := by
  rw [borrow xs i hi]
  rfl

theorem update {α : Type} {n : Usize} (xs : Array α n) (i : Usize)
    (hi : i.val<n.val) (value : α) : Aeneas.Std.Array.update xs i value = .ok (Aeneas.Std.Array.set xs i value) := by
  have hlen : i.val<xs.val.length := by simpa only [xs.property] using hi
  unfold Aeneas.Std.Array.update
  change (match xs.val[i.val]? with
    | none => Result.fail Error.arrayOutOfBounds
    | some _ => Result.ok (Aeneas.Std.Array.set xs i value)) = Result.ok (Aeneas.Std.Array.set xs i value)
  rw [List.getElem?_eq_getElem hlen]

theorem restored_value {α : Type} {n : Usize} (xs : Array α n) (i : Usize)
    (hi : i.val<n.val) (value : α) :
    (Aeneas.Std.Array.set xs i value).val[i.val]'(by simp only [Aeneas.Std.Array.set,List.length_set,xs.property]; exact hi) = value := by
  simp only [Aeneas.Std.Array.set,List.getElem_set_self]

theorem restored_frame {α : Type} {n : Usize} (xs : Array α n) (i j : Usize)
    (hi : i.val<n.val) (hj : j.val<n.val) (hne : i.val ≠ j.val) (value : α) :
    (Aeneas.Std.Array.set xs i value).val[j.val]'(by simp only [Aeneas.Std.Array.set,List.length_set,xs.property]; exact hj) =
      xs.val[j.val]'(by simpa only [xs.property] using hj) := by
  simp only [Aeneas.Std.Array.set,List.getElem_set,if_neg hne]

#print axioms borrow
#print axioms restore
#print axioms update
#print axioms restored_value
#print axioms restored_frame
end PV_B3P_ArrayWrite227
