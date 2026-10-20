import CurrentWideRecordFieldLookupV3
import CurrentWidePolynomialCallbackV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1CurrentWide.Proof

theorem current_polynomial_call_mut_actual_record_field_success
    (bytes : Slice U8)
    (state : E × Slice U8)
    (args : E × Usize)
    (out : E)
    (hmultiplier : CanonicalWide state.1)
    (hacc : CanonicalWide args.1)
    (hcall : current_polynomial_call_mut currentRecordFieldLookup state args =
      .ok (out, state)) :
    ∃ coefficient, currentRecordFieldLookup state.2 args.2 = .ok coefficient ∧
      CanonicalWide coefficient ∧ CanonicalWide out ∧
      decodeWide out = decodeWide args.1 * decodeWide state.1 +
        decodeWide coefficient := by
  exact current_polynomial_call_mut_success currentRecordFieldLookup state args out
    hmultiplier hacc
    (by
      intro input index coefficient hlookup
      exact currentRecordFieldLookup_success_canonical input index coefficient hlookup)
    hcall

#print axioms current_polynomial_call_mut_actual_record_field_success
end AspisR1CurrentWide.Proof
