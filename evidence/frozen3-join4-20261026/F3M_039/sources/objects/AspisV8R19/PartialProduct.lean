import Mathlib.Tactic
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.ZMod.Basic

/-! One Mersenne fold is a residue-preserving, bounded representative.
This justifies delaying canonicalization of the guarded product's two
intermediates; it is not a universal Rust or compiler refinement. -/
set_option autoImplicit false
namespace AspisV8R19.PartialProduct
def p : Nat := 2147483647
def foldOnce (x : Nat) : Nat := x % (p+1) + x / (p+1)

theorem partial_mod (x : Nat) : foldOnce x % p = x % p := by
  have h := congrArg (fun n : Nat => n % p) (Nat.mod_add_div x (p+1))
  simpa [foldOnce,Nat.add_mod,Nat.mul_mod,p] using h

theorem partial_bound (x : Nat) (hx : x < 2*p*p) : foldOnce x < 3*p := by
  have hm := Nat.mod_lt x (show 0 < p+1 by decide)
  have hd : x/(p+1) < 2*p := by
    apply (Nat.div_lt_iff_lt_mul (show 0 < p+1 by decide)).mpr
    simp only [p] at *
    omega
  unfold foldOnce
  omega

theorem product_bound (a b : Nat) (ha : a < p) (hb : b < p) : a*b < p*p := by
  exact Nat.mul_lt_mul_of_lt_of_lt ha hb

theorem intermediate_bounds (cg dh ch dg : Nat)
    (hcg : cg < p*p) (hdh : dh < p*p) (hch : ch < p*p) (hdg : dg < p*p) :
    dh ≤ cg+p*p ∧ cg+p*p < 2^64 ∧ cg+p*p-dh < 2*p*p ∧ ch+dg < 2*p*p := by
  simp only [p] at *
  omega

theorem reconstruction_bounds (ae bf af be u v : Nat)
    (hae : ae < p*p) (hbf : bf < p*p) (haf : af < p*p) (hbe : be < p*p)
    (hu : u < 3*p) (hv : v < 3*p) :
    bf ≤ ae+p*p ∧ ae+p*p < 2^64 ∧
    v ≤ ae+p*p-bf+2*u+3*p ∧ ae+p*p-bf+2*u+3*p < 2^64 ∧
    af+be+u+2*v < 2^64 := by
  simp only [p] at *
  omega

theorem offset_vanishes : (3*p)%p = 0 := by simp

theorem source_fold (x : Nat) : (x &&& p) + (x >>> 31) = foldOnce x := by
  have hp : p = 2^31-1 := rfl
  rw [hp,Nat.and_two_pow_sub_one_eq_mod,Nat.shiftRight_eq_div_pow]
  rfl

theorem partial_cast (x : Nat) : (foldOnce x : ZMod p) = (x : ZMod p) := by
  have h := congrArg (fun n : Nat => (n : ZMod p)) (partial_mod x)
  simpa only [ZMod.natCast_mod] using h

theorem reconstruction_residues (a b c d u v : Nat) :
    ((a : ZMod p)-b+2*(foldOnce u : ZMod p)+3*(p : ZMod p)-(foldOnce v : ZMod p),
     (c : ZMod p)+d+(foldOnce u : ZMod p)+2*(foldOnce v : ZMod p)) =
    ((a : ZMod p)-b+2*(u%p : Nat)+(p : ZMod p)-(v%p : Nat),
     (c : ZMod p)+d+(u%p : Nat)+2*(v%p : Nat)) := by
  simp only [partial_cast,ZMod.natCast_mod,ZMod.natCast_self,mul_zero,add_zero]

#print axioms partial_mod
#print axioms partial_bound
#print axioms product_bound
#print axioms intermediate_bounds
#print axioms reconstruction_bounds
#print axioms offset_vanishes
#print axioms source_fold
#print axioms partial_cast
#print axioms reconstruction_residues
end AspisV8R19.PartialProduct
