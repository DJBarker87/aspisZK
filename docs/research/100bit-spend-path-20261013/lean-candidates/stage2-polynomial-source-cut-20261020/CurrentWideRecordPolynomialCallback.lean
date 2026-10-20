import CurrentWidePolynomialCallbackV1
import CurrentWideRecordFieldLookupV3
set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1CurrentWide.Proof

/-- The emitted current-Wide callback specialized to the actual finish-field
    decoder. This joins callback success inversion to the concrete record
    lookup canonicality owner, without assuming a coefficient trace. -/
theorem current_record_polynomial_call_success
    (bytes : Slice U8)
    (state : E × Slice U8)
    (args : E × Usize)
    (out : E)
    (hmultiplier : CanonicalWide state.1)
    (hacc : CanonicalWide args.1)
    (hcall : current_polynomial_call_mut currentRecordFieldLookup state args =
      .ok (out, state)) :
    ∃ coefficient,
      currentRecordFieldLookup state.2 args.2 = .ok coefficient ∧
      CanonicalWide coefficient ∧ CanonicalWide out ∧
      decodeWide out = decodeWide args.1 * decodeWide state.1 +
        decodeWide coefficient := by
  apply current_polynomial_call_mut_success
  · exact hmultiplier
  · exact hacc
  · intro input i coefficient hlookup
    exact currentRecordFieldLookup_success_canonical input i coefficient hlookup
  · exact hcall

#print axioms current_record_polynomial_call_success

end AspisR1CurrentWide.Proof
