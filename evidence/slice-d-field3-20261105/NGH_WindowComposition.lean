import NGH_AccumulateRef
set_option autoImplicit false
namespace NGH_WindowComposition
open Aeneas Aeneas.Std NGA_Cell

/-- Exact quotient/remainder reconstruction. This is a value law, not an
assumption that any unfinished native window has passed. -/
theorem digit_ext (base a b : Nat) (low : a%base=b%base) (high : a/base=b/base) : a=b := by
 calc
  a = a%base+base*(a/base) := (Nat.mod_add_div a base).symm
  _ = b%base+base*(b/base) := by rw [low,high]
  _ = b := Nat.mod_add_div b base

/-- Finite window composition with the exact final quotient kept explicit. -/
theorem digits_ext (base count a b : Nat)
 (tail : a/base^count=b/base^count)
 (windows : ∀ k<count, (a/base^k)%base=(b/base^k)%base) : a=b := by
 induction count generalizing a b with
 | zero => simpa using tail
 | succ n ih =>
   have high : a/base=b/base := ih (a/base) (b/base)
     (by simpa only [Nat.div_div_eq_div_mul,pow_succ,Nat.mul_comm] using tail)
     (by
       intro k hk
       have h := windows (k+1) (by omega)
       simpa only [Nat.div_div_eq_div_mul,pow_succ,Nat.mul_comm] using h)
   exact digit_ext base a b (by simpa using windows 0 (by omega)) high

/-- Complete typed-array equality once every window of every SAME cell is
available; no independent output arrays or unrelated executions are joined. -/
theorem matrix_ext (base count : Nat) (a b : Sums)
 (tail : ∀ c, (get a c).val/base^count=(get b c).val/base^count)
 (windows : ∀ c k, k<count → ((get a c).val/base^k)%base=((get b c).val/base^k)%base) : a=b := by
 apply NGA_ArrayExt.source
 intro c
 exact digits_ext base count _ _ (tail c) (windows c)

#print axioms digit_ext
#print axioms digits_ext
#print axioms matrix_ext
end NGH_WindowComposition
