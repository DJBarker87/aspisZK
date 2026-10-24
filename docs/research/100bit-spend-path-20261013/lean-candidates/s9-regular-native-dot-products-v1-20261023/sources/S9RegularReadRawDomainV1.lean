import S9ActualRawEbyKBodyV1
import S9NativeFieldDivisionBoundV1
import S9NativePushProductSumV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open AspisR1S9ProductionPairCutV1
namespace AspisR1S9RegularReadRawDomainV1
open AspisR1S9ActualEbyKBackendTransportV1
open AspisR1S9ActualRawEbyKBodyV1

/-- The actual direct regular field read supplies the entire source raw
refinement domain. No caller field-canonicality or scalar-success assumption
is introduced; all scalar rejection paths and accumulator states are kept. -/
theorem regular_read_actual_raw_source_eq
    (f : Slice U8) (n j : Usize) (hj : j.val < n.val)
    (hdiv : (Slice.len f /32#usize : Result Usize)=.ok n)
    (w : NativeW) (hw : weights.field f j=.ok w)
    (dot : fast_pairing.EbyKDot) (scalar : NativeQ) :
    pushWithRaw AspisR1S9ActualRawCutV1.fast_pairing.canonical.Q.raw dot w scalar =
      fast_pairing.EbyKDot.push dot w scalar := by
  have hm := AspisR1S9NativeFieldDivisionBoundV1.quotient_index_maps_s5_reader f n j hdiv hj
  rw [hw] at hm
  have hr := hm.symm
  rw [AspisR1S5PairCutTransparentReaderV1.actualReader_eq_checkedCallback] at hr
  have hcan := AspisR1S5PairCutFieldCallbackV1.checkedFieldCallback_success_push_canonical
    f j (AspisR1S9NativeFieldS5BoundedReaderV1.toS5 w) hr
  rw [AspisR1S9NativePushProductSumV1.native_reader_value_to_source] at hcan
  have hbounds := AspisR1EbyKPowerValueCanonicalToPush.canonical_push_limb_bounds
    (toSourceWide w) hcan
  exact actual_raw_source_body_eq_model dot w scalar hbounds

#print axioms regular_read_actual_raw_source_eq
end AspisR1S9RegularReadRawDomainV1
