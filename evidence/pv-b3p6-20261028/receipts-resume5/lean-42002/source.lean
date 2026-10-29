import PV_B3P_Std194Emission227
namespace PV_B3P_Std194Law227
open Aeneas Aeneas.Std PV_B3P_227
set_option autoImplicit false

/-- The deployed widening body is exactly `small as Self`. -/
theorem u32_u64_result (small : U32) :
    std194227.from_u32_u64 small = .ok (UScalar.cast .U64 small) := rfl

theorem u32_u64_value (small : U32) :
    (UScalar.cast .U64 small).val = small.val := by
  simp only [UScalar.cast_val_eq]
  scalar_tac

/-- The deployed bool body goes through u8; both error layers are retained. -/
theorem bool_u32_result (small : Bool) :
    std194227.from_bool_u32 small = .ok (if small then 1#u32 else 0#u32) := by
  cases small <;> rfl

theorem u16_usize_result (small : U16) :
    std194227.from_u16_usize small = .ok (UScalar.cast .Usize small) := rfl

theorem u16_usize_value (small : U16) :
    (UScalar.cast .Usize small).val = small.val := by
  simp only [UScalar.cast_val_eq]
  scalar_tac

theorem u8_usize_result (small : U8) :
    std194227.from_u8_usize small = .ok (UScalar.cast .Usize small) := rfl

theorem u8_usize_value (small : U8) :
    (UScalar.cast .Usize small).val = small.val := by
  simp only [UScalar.cast_val_eq]
  scalar_tac

#print axioms u32_u64_result
#print axioms u32_u64_value
#print axioms bool_u32_result
#print axioms u16_usize_result
#print axioms u16_usize_value
#print axioms u8_usize_result
#print axioms u8_usize_value
end PV_B3P_Std194Law227
