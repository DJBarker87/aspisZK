import PV_B3P_SelectIndex227
namespace PV_B3P_ArrayWrite227
open Aeneas Aeneas.Std PV_B3P_SelectIndex227
set_option autoImplicit false

theorem borrow {α : Type} {n : Usize} (xs : Array α n) (i : Usize)
    (hi : i.val<n.val) :
    Array.index_mut_usize xs i =
      .ok (xs.val[i.val]'(by simpa only [xs.property] using hi),Array.set xs i) := by
  unfold Array.index_mut_usize
  rw [index_value xs i hi]
  rfl

theorem restore {α : Type} {n : Usize} (xs : Array α n) (i : Usize)
    (hi : i.val<n.val) (change : α → Result α) :
    (do
      let (old,back) ← Array.index_mut_usize xs i
      let updated ← change old
      .ok (back updated)) = (do
      let updated ← change (xs.val[i.val]'(by simpa only [xs.property] using hi))
      .ok (Array.set xs i updated)) := by
  rw [borrow xs i hi]
  rfl

theorem update {α : Type} {n : Usize} (xs : Array α n) (i : Usize)
    (hi : i.val<n.val) (value : α) : Array.update xs i value = .ok (Array.set xs i value) := by
  have hlen : i.val<xs.val.length := by simpa only [xs.property] using hi
  unfold Array.update
  change (match xs.val[i.val]? with
    | none => .fail Error.arrayOutOfBounds
    | some _ => .ok (Array.set xs i value)) = .ok (Array.set xs i value)
  rw [List.getElem?_eq_getElem hlen]

theorem restored_value {α : Type} {n : Usize} (xs : Array α n) (i : Usize)
    (hi : i.val<n.val) (value : α) :
    (Array.set xs i value).val[i.val]'(by simp only [Array.set,List.length_set,xs.property]; exact hi) = value := by
  simp only [Array.set,List.getElem_set_self]

theorem restored_frame {α : Type} {n : Usize} (xs : Array α n) (i j : Usize)
    (hi : i.val<n.val) (hj : j.val<n.val) (hne : i.val ≠ j.val) (value : α) :
    (Array.set xs i value).val[j.val]'(by simp only [Array.set,List.length_set,xs.property]; exact hj) =
      xs.val[j.val]'(by simpa only [xs.property] using hj) := by
  simp only [Array.set,List.getElem_set,if_neg hne]

#print axioms borrow
#print axioms restore
#print axioms update
#print axioms restored_value
#print axioms restored_frame
end PV_B3P_ArrayWrite227
