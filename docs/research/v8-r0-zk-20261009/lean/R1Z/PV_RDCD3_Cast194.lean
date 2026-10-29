import Aeneas

namespace R1Z.PV_RDCD3_Cast194
set_option autoImplicit false
open Aeneas Aeneas.Std

/-- The deployed lossless From macro's complete body is `small as Self`.
The integer-cast primitive remains the existing compiler/Aeneas boundary. -/
theorem u32_u64 (x : U32) :
    core.convert.num.FromU64U32.from x = UScalar.cast .U64 x := rfl

theorem u8_usize (x : U8) :
    core.convert.num.FromUsizeU8.from x = UScalar.cast .Usize x := rfl

theorem u32_u64_val (x : U32) :
    (core.convert.num.FromU64U32.from x).val = x.val := by
  rw [u32_u64]
  scalar_tac

theorem u8_usize_val (x : U8) :
    (core.convert.num.FromUsizeU8.from x).val = x.val := by
  rw [u8_usize]
  scalar_tac

#print axioms u32_u64
#print axioms u8_usize
#print axioms u32_u64_val
#print axioms u8_usize_val
end R1Z.PV_RDCD3_Cast194
