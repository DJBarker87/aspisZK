import S9ActualRawEbyKBodyV1
import S9ActualEbyKPushSourceV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open AspisR1S9ProductionPairCutV1
namespace AspisR1S9ActualRawSourceBackendV1
open AspisR1S9ActualEbyKBackendTransportV1
open AspisR1S9ActualRawEbyKBodyV1
/-- SAME successful current extracted source-body execution, instantiated with
freshly extracted actual Rust raw, reaches the existing S5 concrete backend.
The native input's exact eight bounds are the only domain condition; no
abstract dot meaning, scalar canonicality, child success or target success
premise is supplied. Implementation primitives/runtime remain explicit trust
boundaries, as in the underlying source extraction. -/
theorem actual_source_push_success_backend
    (self out : fast_pairing.EbyKDot) (w : NativeW) (scalar : NativeQ)
    (hw : w.c0.c0.a.val ≤ 2^31-2 ∧ w.c0.c0.b.val ≤ 2^31-2 ∧
      w.c0.c1.a.val ≤ 2^31-2 ∧ w.c0.c1.b.val ≤ 2^31-2 ∧
      w.c1.c0.a.val ≤ 2^31-2 ∧ w.c1.c0.b.val ≤ 2^31-2 ∧
      w.c1.c1.a.val ≤ 2^31-2 ∧ w.c1.c1.b.val ≤ 2^31-2)
    (h : pushWithRaw AspisR1S9ActualRawCutV1.fast_pairing.canonical.Q.raw self w scalar =
      .ok (.Ok (),out)) :
    AspisR1EbyKPushDotBackend.pushWithDotBackend
      AspisR1CanonicalQRawUnified.canonical.Q.raw
      (toSourceState self) (toSourceWide w) (toSourceQ scalar) =
      .ok (.Ok (),toSourceState out) := by
  have he := actual_raw_source_body_eq_model self w scalar hw
  have hmodel : fast_pairing.EbyKDot.push self w scalar = .ok (.Ok (),out) :=
    he.symm.trans h
  have hbackend := AspisR1S9ActualEbyKPushSourceV1.actual_push_success_source_backend
    self out w scalar hmodel
  have hraw : AspisR1S9ActualDotBackendMapV1.actualRaw =
      AspisR1CanonicalQRawUnified.canonical.Q.raw :=
    funext (fun a => funext (fun b =>
      AspisR1S9ActualRawHookIdentityV1.actual_raw_eq_source a b))
  rw [←hraw]
  exact hbackend
#print axioms actual_source_push_success_backend
end AspisR1S9ActualRawSourceBackendV1
