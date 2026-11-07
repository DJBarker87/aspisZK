import NMT_345RSLCarriers
set_option autoImplicit false
namespace NMT_R2_SmallAdd
open Aeneas Aeneas.Std

/-- A generic checked-add law on the exact original scalar arguments. -/
theorem checked_add (a b c : Usize) (sum : a.val + b.val = c.val) :
 (a + b : Result Usize) = .ok c := by
 have bounds : UScalar.inBounds .Usize (a.val + b.val) := by
  rw [sum]
  unfold UScalar.inBounds
  scalar_tac
 have law := UScalar.add_equiv a b
 cases hr : (a + b : Result Usize) with
 | fail e =>
  rw [hr] at law
  exact False.elim (law bounds)
 | div =>
  rw [hr] at law
  exact False.elim law
 | ok d =>
  rw [hr] at law
  have same : d = c := UScalar.eq_of_val_eq (law.2.1.trans sum)
  rw [same]
#print axioms checked_add
end NMT_R2_SmallAdd
