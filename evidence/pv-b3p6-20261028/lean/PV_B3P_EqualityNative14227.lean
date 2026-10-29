import PV_B3P_TransitionLoan14227
import PV_B3P_EqualityBinding9227
import PV_B3P_EqualityLink13227
namespace PV_B3P_Loans14227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227
set_option autoImplicit false
abbrev EqualityInput14 := Array aspis_core.field.QM31 10#usize
/-- Frozen source's two immutable loans and increasing while loop. Aliased
loans are allowed: neither input is written and no address is inspected. -/
def equality_native14 (left right : Shared14 EqualityInput14) : Result aspis_core.field.QM31 := do
  let l ← Array.index_usize left.value 0#usize
  let r ← Array.index_usize right.value 0#usize
  let product ← reference_terminal.equality_factor l r
  source_equality_loop left.value right.value product 1#usize

theorem equality_native_binding14 (left right : Shared14 EqualityInput14) :
    equality_native14 left right = reference_terminal.equality_value left.value right.value :=
  equality_body_binding left.value right.value

theorem equality_source_length14 (left : Shared14 EqualityInput14) :
    left.value.val.length = (10#usize).val := left.value.property

theorem equality_source_read_bound14 (index : Usize) (guard : index < 10#usize) :
    index.val < (10#usize).val := by scalar_tac

theorem equality_native_continuation14 {β : Type} (left right : Shared14 EqualityInput14)
    (next : aspis_core.field.QM31 → Result β) :
    (do let result ← equality_native14 left right; next result) =
      (do let result ← reference_terminal.equality_value left.value right.value; next result) := by
  rw [equality_native_binding14]
#print axioms equality_native_binding14
#print axioms equality_source_length14
#print axioms equality_source_read_bound14
#print axioms equality_native_continuation14
end PV_B3P_Loans14227
