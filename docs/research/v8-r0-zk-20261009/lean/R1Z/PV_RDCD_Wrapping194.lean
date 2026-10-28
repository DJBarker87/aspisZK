import Aeneas
set_option autoImplicit false
namespace R1Z.PV_RDCD_Wrapping194
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
#print axioms add32_binding
#print axioms sub32_binding
#print axioms add64_binding
#print axioms mul64_binding
#print axioms shift_mask
#print axioms shr64_binding
end R1Z.PV_RDCD_Wrapping194
