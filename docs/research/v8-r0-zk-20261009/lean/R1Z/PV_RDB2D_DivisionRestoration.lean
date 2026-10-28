import R1Z.PV_RDB2D_SamplerCore
namespace R1Z.PV_RDB2D_SamplerRestoration
open Aeneas Aeneas.Std Result ControlFlow PV_B2_C_Sampler
set_option autoImplicit false
abbrev Words := Array U32 8#usize

def borrow (current : Words) (index : Usize) : Result (U32 × (Words → U32 → Result Words)) := do
  let word ← Array.index_usize current index
  ok (word,fun now value => Array.update now index value)

theorem restoration (current now : Words) (index : Usize) (word : U32)
    (read : Array.index_usize current index=ok word) :
    borrow current index=ok (word,fun valueStore replacement => Array.update valueStore index replacement) := by
  simp only [borrow,read,bind_tc_ok]
#print axioms restoration
def divisionBody
  (quotient : Array Std.U32 8#usize) (remainder : Std.U64) (j : Std.Usize) :
  Result (ControlFlow ((Array Std.U32 8#usize) × Std.U64 × Std.Usize) ((Array
    Std.U32 8#usize) × Std.U64))
  := do
  if j > 0#usize
  then
    let j1 ← lift (Std.Usize.wrapping_sub j 1#usize)
    let i ← lift (Std.U64.wrapping_shl remainder 32#u32)
    let (i1,back) ← borrow quotient j1
    let i2 ← lift (core.convert.num.FromU64U32.from i1)
    let dividend ← lift (i ||| i2)
    let i3 ← lift (core.convert.num.FromU64U32.from aspis_core.field.P)
    let i4 ← dividend / i3
    let i5 ← lift (UScalar.cast .U32 i4)
    let quotient1 ← back quotient i5
    let i6 ← lift (core.convert.num.FromU64U32.from aspis_core.field.P)
    let remainder1 ← dividend % i6
    ok (cont (quotient1, remainder1, j1))
  else ok (done (quotient, remainder))

theorem division_body (q : Words) (r : U64) (j : Usize) :
    divisionBody q r j=host_sampler.low_base_p_digits_loop1_loop0.body q r j := by
  simp only [divisionBody,host_sampler.low_base_p_digits_loop1_loop0.body,borrow,bind_assoc_eq,bind_tc_ok]
  rfl
#print axioms division_body
end R1Z.PV_RDB2D_SamplerRestoration
