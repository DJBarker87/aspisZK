import S9ActualEbyKPushSourceV1
import S5QRaw.EbyKPushDecodedProductUpdateV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9ActualEbyKRawAliasV1
/-- Pointwise identity of the exact source-owned raw function used by current
native Dot and by the retained S5 decoded-product consumer. -/
theorem actual_raw_eq_source (a b : Array U32 4#usize) :
    AspisR1S9ActualDotBackendMapV1.actualRaw a b =
      AspisR1EbyKPushDecodedProductUpdate.QRaw a b := by
  rfl

/-- The same accepted native push reaches the retained S5 product backend,
with its existing raw function explicitly identified rather than renamed. -/
theorem actual_push_success_s5_backend
    (self out : AspisR1S9ProductionPairCutV1.fast_pairing.EbyKDot)
    (value : AspisR1S9ActualEbyKBackendTransportV1.NativeW)
    (scalar : AspisR1S9ActualEbyKBackendTransportV1.NativeQ)
    (h : AspisR1S9ProductionPairCutV1.fast_pairing.EbyKDot.push self value scalar =
      .ok (.Ok (),out)) :
    AspisR1EbyKPushDotBackend.pushWithDotBackend AspisR1EbyKPushDecodedProductUpdate.QRaw
      (AspisR1S9ActualEbyKBackendTransportV1.toSourceState self)
      (AspisR1S9ActualEbyKBackendTransportV1.toSourceWide value)
      (AspisR1S9ActualEbyKBackendTransportV1.toSourceQ scalar) =
      .ok (.Ok (),AspisR1S9ActualEbyKBackendTransportV1.toSourceState out) := by
  have he : AspisR1S9ActualDotBackendMapV1.actualRaw = AspisR1EbyKPushDecodedProductUpdate.QRaw :=
    funext (fun a => funext (fun b => actual_raw_eq_source a b))
  rw [←he]
  exact AspisR1S9ActualEbyKPushSourceV1.actual_push_success_source_backend self out value scalar h

#print axioms actual_raw_eq_source
#print axioms actual_push_success_s5_backend
end AspisR1S9ActualEbyKRawAliasV1
