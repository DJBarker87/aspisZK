import NDO_JHd_RequestDecode
import NDO_JHd_RequestCarrier
set_option autoImplicit false
namespace AspisR1.JHd_RequestNative
open Aeneas Aeneas.Std Result
abbrev Request := AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalRequestV1
abbrev FormatError := AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1

/-- Slice wrapper for the extracted ASQ8 reference decoder, retaining every
error constructor through the explicit carrier map. Native/reference codec
association remains a separate source obligation. -/
def decode (bytes : Slice U8) : Result (core.result.Result Request FormatError) := do
  let array ← core.array.TryFromSharedArraySlice.try_from 320#usize bytes
  match array with
  | .Err _=>ok (.Err .WrongLength)
  | .Ok array=>
    let result ← AspisR20Request.pool_v1.pair_forest_terminal.decode_pool_v1_pair_forest_terminal_request_reference_v1 array
    match result with
    | .Err error=>ok (.Err (JHd_RequestCarrier.mapPoolV1PairForestTerminalFormatErrorV1 error))
    | .Ok request=>ok (.Ok (JHd_RequestCarrier.request request))

attribute [local irreducible] JHb_DataRequest.value JHd_RequestWindow.value

theorem shared : core.array.TryFromSharedArraySlice.try_from 320#usize JHb_DataRequest.value=
    ok (.Ok JHd_RequestWindow.value) := by
  apply JFs_ArrayWindow.shared
  unfold JHb_DataRequest.value JHd_RequestWindow.value
  rfl
#print axioms shared

theorem source : decode JHb_DataRequest.value=ok (.Ok JHd_RequestCarrier.actual) := by
  unfold decode
  simp only [shared,bind_tc_ok,JHd_RequestDecode.source]
  rfl
#print axioms source
end AspisR1.JHd_RequestNative
