import Mathlib.Data.ZMod.Basic
set_option autoImplicit false
namespace PV_L2C_M31
abbrev p : Nat := 2147483647
abbrev word := BitVec 32
def canonical (x : word) : Prop := x.toNat < p
/-- Literal wrapping mask/subtract projection of field/ct.rs::subtract_p. -/
def subtractP (x : word) : word :=
  x - ((BitVec.ofNat 32 p) &&& (0 - (if p ≤ x.toNat then 1 else 0)))
def add (x y : word) : word := subtractP (x+y)
def sub (x y : word) : word := subtractP (x + BitVec.ofNat 32 p - y)
def decode (x : word) : ZMod p := x.toNat

theorem subtractP_branch (x : word) :
    subtractP x = if p ≤ x.toNat then x-BitVec.ofNat 32 p else x := by
  unfold subtractP
  split <;> simp_all [BitVec.zero_sub,BitVec.neg_one_eq_allOnes]
#print axioms subtractP_branch

theorem subtractP_nat (x : word) :
    (subtractP x).toNat = if p ≤ x.toNat then x.toNat-p else x.toNat := by
  rw [subtractP_branch]
  split
  · rename_i h
    rw [BitVec.toNat_sub]
    simp only [BitVec.toNat_ofNat]
    have hx := x.isLt
    omega
  · rfl
#print axioms subtractP_nat

theorem subtractP_canonical (x : word) (hx : x.toNat<2*p) : canonical (subtractP x) := by
  unfold canonical
  rw [subtractP_nat]
  split <;> omega
#print axioms subtractP_canonical

theorem add_nat (x y : word) (hx : canonical x) (hy : canonical y) :
    (add x y).toNat = if p ≤ x.toNat+y.toNat then x.toNat+y.toNat-p else x.toNat+y.toNat := by
  unfold add
  rw [subtractP_nat,BitVec.toNat_add,Nat.mod_eq_of_lt (show x.toNat+y.toNat<2^32 by unfold canonical at *; omega)]
#print axioms add_nat

theorem add_canonical (x y : word) (hx : canonical x) (hy : canonical y) :
    canonical (add x y) := by
  unfold canonical
  rw [add_nat x y hx hy]
  unfold canonical at hx hy
  split <;> omega
#print axioms add_canonical

theorem add_decode (x y : word) (hx : canonical x) (hy : canonical y) :
    decode (add x y) = decode x+decode y := by
  unfold decode
  rw [add_nat x y hx hy]
  split
  · rename_i h
    rw [Nat.cast_sub h,Nat.cast_add]
    simp
  · exact Nat.cast_add _ _
#print axioms add_decode
end PV_L2C_M31
