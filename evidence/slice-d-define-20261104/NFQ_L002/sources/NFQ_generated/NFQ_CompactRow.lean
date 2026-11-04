import NCO_ScalarBridge
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NFQ_CompactRow
/-- All u8 inputs: reuse the extracted Rust reference, no restricted row domain. -/
theorem reference (row : U8) :
    NCO_Reference.compact_row_ref row = AspisS1NativeCompact.compact.compact_row row :=
  NCO_ScalarBridge.compact_row row
#print axioms reference
end NFQ_CompactRow
