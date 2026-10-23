import S9ActualRawEbyKBodyV1
import S9PartialDotReaderDomainV1
import S9NativePushProductSumV1
import S9SharedPartialsReadBindingsV1
import S9NativeWidePushCanonicalV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open AspisR1S9ProductionPairCutV1
namespace AspisR1S9PartialHighRawDomainV1
open AspisR1S9ActualEbyKBackendTransportV1
open AspisR1S9ActualRawEbyKBodyV1
open AspisR1S9PartialDotReaderDomainV1
open AspisR1S9FactorArrayEntryV1

/-- The SAME successful partial-prefix field read supplies the complete raw
source-refinement domain. No separate native canonicality assumption. This
proves full EbyK source-body replacement for every scalar/count/accumulator. -/
theorem partial_read_actual_raw_source_eq
    (f : Slice U8) (s j : Usize) (hs : s.val < 4) (hj : j.val < 16)
    (hdiv : (Slice.len f /32#usize : Result Usize)=.ok (64#usize))
    (w : NativeW) (hw : weights.field f (index s j)=.ok w)
    (dot : fast_pairing.EbyKDot) (scalar : NativeQ) :
    pushWithRaw AspisR1S9ActualRawCutV1.fast_pairing.canonical.Q.raw dot w scalar =
      fast_pairing.EbyKDot.push dot w scalar := by
  have hm := index_maps_s5_reader f s j hs hj hdiv
  rw [hw] at hm
  have hr := hm.symm
  rw [AspisR1S5PairCutTransparentReaderV1.actualReader_eq_checkedCallback] at hr
  have hcan := AspisR1S5PairCutFieldCallbackV1.checkedFieldCallback_success_push_canonical
    f (index s j) (AspisR1S9NativeFieldS5BoundedReaderV1.toS5 w) hr
  rw [AspisR1S9NativePushProductSumV1.native_reader_value_to_source] at hcan
  have hbounds := AspisR1EbyKPowerValueCanonicalToPush.canonical_push_limb_bounds
    (toSourceWide w) hcan
  exact actual_raw_source_body_eq_model dot w scalar hbounds

/-- The SAME accepted shared-partials producer and SAME input read supply
all native bounds needed by actual C raw. No independent high-input Can or
per-push/scalar-check/finish success is assumed. -/
theorem shared_high_read_actual_raw_source_eq
    (f : Slice U8) (common : Array NativeQ 16#usize) (partials : Array NativeW 4#usize)
    (hproducer : weights.shared_partials f common=.ok (.Ok partials))
    (j : Usize) (hj : j.val < 4) (w : NativeW)
    (hw : Array.index_usize partials j=.ok w)
    (dot : fast_pairing.EbyKDot) (scalar : NativeQ) :
    pushWithRaw AspisR1S9ActualRawCutV1.fast_pairing.canonical.Q.raw dot w scalar =
      fast_pairing.EbyKDot.push dot w scalar := by
  have hdata := AspisR1S9SharedPartialsReadBindingsV1.actual_shared_partials_output_canonical
    f common partials hproducer
  have hew := accepted_index_eq_atN partials j hj w hw
  have hcan : AspisR1S9ActualPairWideCanonicalV1.Canonical w := by
    rw [hew]
    exact hdata j hj
  exact actual_raw_source_body_eq_model dot w scalar
    (AspisR1S9NativeWidePushCanonicalV1.native_canonical_eight_bounds w hcan)

#print axioms partial_read_actual_raw_source_eq
#print axioms shared_high_read_actual_raw_source_eq
end AspisR1S9PartialHighRawDomainV1
