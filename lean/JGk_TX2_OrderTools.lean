import JGk_TX2_ComparatorTransport
import Mathlib.Data.Multiset.Basic
set_option autoImplicit false
namespace AspisR1.JGk_TX2_OrderTools

def le (a b : Nat × Nat) : Prop := a.1 < b.1 ∨ a.1 = b.1 ∧ a.2 ≤ b.2
instance : DecidableRel le := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

theorem trans (a b c : Nat × Nat) (ab : le a b) (bc : le b c) : le a c := by
  unfold le at *
  omega
#print axioms trans

theorem total (a b : Nat × Nat) : le a b ∨ le b a := by
  unfold le
  omega
#print axioms total

theorem antisymm (a b : Nat × Nat) (ab : le a b) (ba : le b a) : a=b := by
  have h1 : a.1=b.1 := by unfold le at *; omega
  have h2 : a.2=b.2 := by unfold le at *; omega
  exact Prod.ext h1 h2
#print axioms antisymm

theorem sorted_permutation (xs ys : List (Nat × Nat))
    (perm : xs.Perm ys) (sorted : ys.Pairwise le) :
    xs.mergeSort (fun a b => decide (le a b))=ys := by
  have ordered : (xs.mergeSort (fun a b => decide (le a b))).Pairwise le := by
    simpa only [decide_eq_true_eq] using List.pairwise_mergeSort
      (le := fun a b => decide (le a b))
      (by simpa only [decide_eq_true_eq] using trans)
      (by intro a b; simpa using total a b) xs
  exact ((List.mergeSort_perm _ _).trans perm).eq_of_pairwise
    (fun a b _ _ => antisymm a b) ordered sorted
#print axioms sorted_permutation

theorem append_groups (h : Nat) (a b : List (Nat × Nat))
    (sa : a.Pairwise le) (sb : b.Pairwise le)
    (ha : ∀ x ∈ a, x.1=h) (hb : ∀ x ∈ b, h<x.1) :
    (a++b).Pairwise le := by
  apply List.pairwise_append.mpr
  refine ⟨sa,sb,?_⟩
  intro x hx y hy
  exact Or.inl (by rw [ha x hx]; exact hb y hy)
#print axioms append_groups
end AspisR1.JGk_TX2_OrderTools
