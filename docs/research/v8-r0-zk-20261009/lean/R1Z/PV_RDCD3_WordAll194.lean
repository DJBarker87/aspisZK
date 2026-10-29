import R1Z.PV_RDCD3_Word194

namespace R1Z.PV_RDCD3_WordAll194
set_option autoImplicit false
open Aeneas Aeneas.Std

/-- The selected uint macro delegates these operations to the corresponding
integer intrinsic. The intrinsic interpretation is the existing bitvector
primitive boundary, not a proof about LLVM or the machine observer. -/
def add {ty : UScalarTy} (x y : UScalar ty) : UScalar ty := (x.bv+y.bv)#uscalar
def sub {ty : UScalarTy} (x y : UScalar ty) : UScalar ty := (x.bv-y.bv)#uscalar
def mul {ty : UScalarTy} (x y : UScalar ty) : UScalar ty := (x.bv*y.bv)#uscalar

theorem add_binding {ty : UScalarTy} (x y : UScalar ty) :
    add x y = UScalar.wrapping_add x y := rfl

theorem sub_binding {ty : UScalarTy} (x y : UScalar ty) :
    sub x y = UScalar.wrapping_sub x y := rfl

theorem mul_binding {ty : UScalarTy} (x y : UScalar ty) :
    mul x y = UScalar.wrapping_mul x y := rfl

theorem sub64_binding (x y : U64) : sub x y = U64.wrapping_sub x y := rfl

theorem subUsize_binding (x y : Usize) : sub x y = Usize.wrapping_sub x y := rfl

#print axioms add_binding
#print axioms sub_binding
#print axioms mul_binding
#print axioms sub64_binding
#print axioms subUsize_binding
end R1Z.PV_RDCD3_WordAll194
