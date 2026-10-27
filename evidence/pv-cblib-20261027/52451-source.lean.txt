import R1Z.PV_CBL_FinalSoft
open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_Suffix64Value
set_option autoImplicit false
def value (w : U64) : Array U8 8#usize :=
  Array.make 8#usize [UScalar.cast .U8 (U64.wrapping_shr w 56#u32),UScalar.cast .U8 (U64.wrapping_shr w 48#u32),UScalar.cast .U8 (U64.wrapping_shr w 40#u32),UScalar.cast .U8 (U64.wrapping_shr w 32#u32),UScalar.cast .U8 (U64.wrapping_shr w 24#u32),UScalar.cast .U8 (U64.wrapping_shr w 16#u32),UScalar.cast .U8 (U64.wrapping_shr w 8#u32),UScalar.cast .U8 w]
theorem source (w : U64) : PV_CBL_FinalSoft.sha_length_suffix64 w = ok (value w) := rfl
#print axioms value
#print axioms source
end R1Z.PV_CBL_Suffix64Value
