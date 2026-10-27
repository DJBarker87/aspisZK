import LPm_UpdatePort
import JGi_PushTotality
set_option autoImplicit false
namespace AspisR1.LPm_DotPort
open Aeneas Aeneas.Std Result
open LPm_RawPort LPm_UpdatePort

theorem private_call (s : LPm_PublicState.Dot)
    (a b : FIo_Native.fast_pairing.canonical.Q) (raw : LPm_PublicState.Raw)
    (call : FIo_Native.fast_pairing.canonical.Q.raw a b=ok raw) :
    AspisR1EbyKPushDotBackend.dotViaRaw AspisR1EbyKPushDecodedProductUpdate.QRaw
      (dotPort s) a b=ok (dotPort (LPm_PublicState.update s raw)) := by
  have modelRaw : AspisR1EbyKPushDecodedProductUpdate.QRaw a b=ok raw := by
    rw [raw_eq]
    exact call
  have model := AspisR1DotPushLocal.Proof.push_total_from_raw
    AspisR1EbyKPushDecodedProductUpdate.QRaw ⟨s.sums⟩ a b raw modelRaw
  simp only [AspisR1EbyKPushDotBackend.dotViaRaw,dotPort,model,bind_tc_ok]
  rw [← sums s raw]

#print axioms private_call
#check AspisR1S5EbyKPushTotalityV1.push_success_of_valid_scalar
end AspisR1.LPm_DotPort
