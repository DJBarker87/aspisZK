import NCO_ScalarBridge
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NFQ_CompactRow
/-- Complete scalar reply and unchanged state/empty effects of compact_row. -/
theorem result_state_effects (row : U8) (state : Nat) :
    (NCO_Reference.compact_row_ref row, state, ([] : List Nat)) =
    (AspisS1NativeCompact.compact.compact_row row, state, []) := by
  rw [NCO_ScalarBridge.compact_row]
#print axioms result_state_effects
end NFQ_CompactRow
