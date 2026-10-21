import R22TotalCheckedComposition

/-! Kernel-checked unsigned primitive instances of the composition rule.
Casts are bitvector conversions, not checked failures on lost high bits. -/
set_option autoImplicit false
namespace AspisR1.R22TotalUnsignedPrimitives
open Aeneas Aeneas.Std Result R22TotalCheckedComposition

theorem add_success {ty : UScalarTy} (x y z : UScalar ty)
    (h : UScalar.add x y = ok z) :
    UScalar.wrapping_add x y = z ∧ x.val + y.val < 2^ty.numBits := by
  have he := UScalar.add_equiv x y
  have hop : (x+y : Result (UScalar ty)) = UScalar.add x y := rfl
  simp only [hop,h] at he
  refine ⟨?_,he.1⟩
  apply UScalar.eq_of_val_eq
  change (x.bv+y.bv).toNat = z.bv.toNat
  exact congrArg BitVec.toNat he.2.2.symm

theorem sub_success {ty : UScalarTy} (x y z : UScalar ty)
    (h : UScalar.sub x y = ok z) :
    UScalar.wrapping_sub x y = z ∧ y.val ≤ x.val := by
  have he := UScalar.sub_equiv x y
  have hop : (x-y : Result (UScalar ty)) = UScalar.sub x y := rfl
  simp only [hop,h] at he
  refine ⟨?_,he.1⟩
  apply UScalar.eq_of_val_eq
  change (x.bv-y.bv).toNat = z.bv.toNat
  exact congrArg BitVec.toNat he.2.2.symm

theorem mul_success {ty : UScalarTy} (x y z : UScalar ty)
    (h : UScalar.mul x y = ok z) :
    UScalar.wrapping_mul x y = z ∧ x.val*y.val < 2^ty.numBits := by
  have he := UScalar.mul_equiv x y
  have hop : (x*y : Result (UScalar ty)) = UScalar.mul x y := rfl
  simp only [hop,h] at he
  refine ⟨?_,?_⟩
  · apply UScalar.eq_of_val_eq
    change (x.bv*y.bv).toNat = z.bv.toNat
    exact congrArg BitVec.toNat he.2.2.symm
  · have hb := he.1
    rw [UScalar.max] at hb
    have hp : 0 < 2^ty.numBits := Nat.pow_pos (by decide)
    omega

def addPrimitive {ty : UScalarTy} (x y : UScalar ty) : Primitive (UScalar ty) where
  checked := UScalar.add x y
  wrapping := UScalar.wrapping_add x y
  safe := x.val + y.val < 2^ty.numBits
  success v h := (add_success x y v h).symm

def subPrimitive {ty : UScalarTy} (x y : UScalar ty) : Primitive (UScalar ty) where
  checked := UScalar.sub x y
  wrapping := UScalar.wrapping_sub x y
  safe := y.val ≤ x.val
  success v h := (sub_success x y v h).symm

def mulPrimitive {ty : UScalarTy} (x y : UScalar ty) : Primitive (UScalar ty) where
  checked := UScalar.mul x y
  wrapping := UScalar.wrapping_mul x y
  safe := x.val*y.val < 2^ty.numBits
  success v h := (mul_success x y v h).symm

/-- Rust unsigned `as` casts have modulo semantics. Totality cannot establish
that a narrowing conversion preserves its unbounded mathematical value. -/
theorem cast_mod {ty : UScalarTy} (x : UScalar ty) (target : UScalarTy) :
    (UScalar.cast target x).val = x.val % 2^target.numBits := by
  simp only [UScalar.cast, UScalar.val, BitVec.toNat_setWidth]

theorem cast_exact {ty : UScalarTy} (x : UScalar ty) (target : UScalarTy)
    (h : x.val < 2^target.numBits) : (UScalar.cast target x).val = x.val := by
  rw [cast_mod, Nat.mod_eq_of_lt h]

/-- A literal truncating cast is safe for machine agreement even if lossy. -/
def castPrimitive {ty : UScalarTy} (x : UScalar ty) (target : UScalarTy) :
    Primitive (UScalar target) where
  checked := ok (UScalar.cast target x)
  wrapping := UScalar.cast target x
  safe := True
  success v h := ⟨True.intro, Result.ok.inj h⟩

/-- Concrete obstruction to deriving safety from wrapping acceptance. -/
theorem wrapping_success_is_insufficient :
    UScalar.wrapping_add (255#u8) (1#u8) = (0#u8) ∧
      UScalar.add (255#u8) (1#u8) ≠ ok (0#u8) := by
  constructor
  · rfl
  · intro h
    have hb := (add_success _ _ _ h).2
    change 255 + 1 < 256 at hb
    omega

#print axioms add_success
#print axioms sub_success
#print axioms mul_success
#print axioms cast_mod
#print axioms cast_exact
#print axioms wrapping_success_is_insufficient
end AspisR1.R22TotalUnsignedPrimitives
