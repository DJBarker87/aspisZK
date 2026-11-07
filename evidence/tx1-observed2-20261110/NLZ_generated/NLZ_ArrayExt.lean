import NLZ_VerifiedExt
set_option autoImplicit false
namespace AspisR1.NLZ_ArrayExt
open Aeneas Aeneas.Std
/-- Pointwise value composition for arbitrary-offset native windows. No large
concrete array is evaluated, and no physical pointer conclusion is inferred. -/
theorem list_ext {α : Type} (a b : List α) (cells : ∀ i : Nat, a[i]? = b[i]?) : a=b := by
 induction a generalizing b with
 | nil =>
   cases b with
   | nil => rfl
   | cons bh bt => have h:=cells 0;cases h
 | cons ah tailA ih =>
   cases b with
   | nil => have h:=cells 0;cases h
   | cons bh bt =>
     have heads : ah=bh := Option.some.inj (cells 0)
     have tails : tailA=bt := ih bt (fun i => cells (i+1))
     cases heads
     cases tails
     rfl

theorem outside {α : Type} (a : List α) (i : Nat) (bound : a.length  ≤  i) : a[i]? = none := by
 induction a generalizing i with
 | nil => rfl
 | cons h t ih =>
   cases i with
   | zero => change t.length+1 ≤ 0 at bound;omega
   | succ i =>
     apply ih
     change t.length+1 ≤ i+1 at bound
     omega

theorem array_ext {α : Type} {n : Usize} (a b : Aeneas.Std.Array α n)
 (cells : ∀ i : Nat, i<n.val → a.val[i]? = b.val[i]?) : a=b := by
 have same : a.val=b.val := by
  apply list_ext
  intro i
  by_cases inside : i<n.val
  · exact cells i inside
  · have left := a.property
    have right := b.property
    rw [outside a.val i (by omega),outside b.val i (by omega)]
 cases a
 cases b
 cases same
 rfl
#print axioms list_ext
#print axioms outside
#print axioms array_ext
end AspisR1.NLZ_ArrayExt
