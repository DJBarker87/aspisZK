import Aeneas
set_option autoImplicit false
namespace R1Z.PV_RDCD3_Word194
open Aeneas Aeneas.Std
/- Source bodies are the pinned uint_impl! macro methods. Intrinsics are
   interpreted at the existing bitvector primitive boundary, not proved LLVM. -/
def add32 (x y : U32) : U32 := (x.bv + y.bv)#uscalar
def sub32 (x y : U32) : U32 := (x.bv - y.bv)#uscalar
def add64 (x y : U64) : U64 := (x.bv + y.bv)#uscalar
def mul64 (x y : U64) : U64 := (x.bv * y.bv)#uscalar
def shr64 (x : U64) (rhs : U32) : U64 :=
  (x.bv.ushiftRight (rhs.val &&& (64 - 1)))#uscalar
theorem add32_binding (x y : U32) : add32 x y = core.num.U32.wrapping_add x y := rfl
theorem sub32_binding (x y : U32) : sub32 x y = core.num.U32.wrapping_sub x y := rfl
theorem add64_binding (x y : U64) : add64 x y = U64.wrapping_add x y := rfl
theorem mul64_binding (x y : U64) : mul64 x y = U64.wrapping_mul x y := rfl
theorem shift_mask (rhs : Nat) : rhs &&& (64 - 1) = rhs % 64 := by
  exact Nat.and_two_pow_sub_one_eq_mod rhs 6
theorem shr64_binding (x : U64) (rhs : U32) : shr64 x rhs = U64.wrapping_shr x rhs := by
  simp only [shr64, shift_mask, U64.wrapping_shr, UScalar.wrapping_shr]
  rfl
/-- 1.94.1 wrapping_shr at the u16 instantiation used by inactive masks. -/
def shr16 (x : U16) (rhs : U32) : U16 :=
  (x.bv.ushiftRight (rhs.val &&& (16-1)))#uscalar

theorem shr16_binding (x : U16) (rhs : U32) : shr16 x rhs = U16.wrapping_shr x rhs := by
  have mask : rhs.val &&& (16-1) = rhs.val % 16 := Nat.and_two_pow_sub_one_eq_mod rhs.val 4
  simp only [shr16,mask,U16.wrapping_shr,UScalar.wrapping_shr]
  rfl

theorem unchecked16_bound (rhs : Nat) : rhs &&& (16-1) < 16 := by
  rw [Nat.and_two_pow_sub_one_eq_mod rhs 4]
  exact Nat.mod_lt _ (by decide)

theorem unchecked64_bound (rhs : Nat) : rhs &&& (64-1) < 64 := by
  rw [shift_mask]
  exact Nat.mod_lt _ (by decide)

/-- Native plain shifts and model wrapping shifts agree on the proved native
precondition. This is a bitvector primitive boundary, never an LLVM proof. -/
def directShr {ty : UScalarTy} (x : UScalar ty) (rhs : U32) : UScalar ty :=
  (x.bv.ushiftRight rhs.val)#uscalar

def directShl {ty : UScalarTy} (x : UScalar ty) (rhs : U32) : UScalar ty :=
  (x.bv.shiftLeft rhs.val)#uscalar

theorem boundedShr {ty : UScalarTy} (x : UScalar ty) (rhs : U32)
    (bound : rhs.val < ty.numBits) :
    UScalar.wrapping_shr x rhs = directShr x rhs := by
  simp only [UScalar.wrapping_shr,directShr,Nat.mod_eq_of_lt bound]

theorem boundedShl {ty : UScalarTy} (x : UScalar ty) (rhs : U32)
    (bound : rhs.val < ty.numBits) :
    UScalar.wrapping_shl x rhs = directShl x rhs := by
  simp only [UScalar.wrapping_shl,directShl,Nat.mod_eq_of_lt bound]

theorem cast_false : UScalar.cast_fromBool .U32 false = 0#u32 := rfl
theorem cast_true : UScalar.cast_fromBool .U32 true = 1#u32 := rfl

#print axioms shr16_binding
#print axioms unchecked16_bound
#print axioms unchecked64_bound
#print axioms boundedShr
#print axioms boundedShl
#print axioms cast_false
#print axioms cast_true
#print axioms add32_binding
#print axioms sub32_binding
#print axioms add64_binding
#print axioms mul64_binding
#print axioms shift_mask
#print axioms shr64_binding
end R1Z.PV_RDCD3_Word194
