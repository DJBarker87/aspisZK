import R1Z.PV_RDB2D_DivisionRestoration
namespace R1Z.PV_RDB2D_SamplerRestoration
open Aeneas Aeneas.Std Result ControlFlow PV_B2_C_Sampler
set_option autoImplicit false
def carryBody
  (digits : Array Std.U32 8#usize) (addend : Std.U32) (i : Std.Usize) :
  Result (ControlFlow ((Array Std.U32 8#usize) × Std.U32 × Std.Usize) ((Array
    Std.U32 8#usize) × Std.U32))
  := do
  if i < 8#usize
  then
    let (i1,back) ← borrow digits i
    let i2 ← lift (core.convert.num.FromU64U32.from i1)
    let i3 ← lift (core.convert.num.FromU64U32.from addend)
    let sum ← lift (Std.U64.wrapping_add i2 i3)
    let i4 ← lift (core.convert.num.FromU64U32.from aspis_core.field.P)
    let i5 ← sum % i4
    let i6 ← lift (UScalar.cast .U32 i5)
    let digits1 ← back digits i6
    let i7 ← lift (core.convert.num.FromU64U32.from aspis_core.field.P)
    let i8 ← sum / i7
    let addend1 ← lift (UScalar.cast .U32 i8)
    let i9 ← lift (Std.Usize.wrapping_add i 1#usize)
    ok (cont (digits1, addend1, i9))
  else ok (done (digits, addend))

theorem carry_body (q : Words) (r : U32) (j : Usize) :
    carryBody q r j=host_sampler.add_small_base_p_loop.body q r j := by
  simp only [carryBody,host_sampler.add_small_base_p_loop.body,borrow,bind_assoc_eq,bind_tc_ok]
  rfl
#print axioms carry_body
end R1Z.PV_RDB2D_SamplerRestoration
