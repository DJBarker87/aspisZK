import S9ActiveFourCanonicalV1
import S9ActualPairHelperLoopToOldV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9FactoredActiveCanonicalV1
open AspisR1S9ProductionPairCutV1
open AspisR1S9NativeArrayCanonicalV1
variable [allocation : AspisR1S9AllocationInterfaceV1.Allocation]
/-- The actual private four-weight producer discharges the active loop's
coefficient canonicality premise. Both events are the native source functions;
source parent sequencing is supplied by its separately proved event trace. -/
theorem factored_active_success_canonical
    (ap0 ap1 : Array W 4#usize) (extra : Array aspis_core.field.QM31 2#usize)
    (libra : Array W 4#usize) (f : Slice U8) (parts out : Array W 7#usize)
    (hp0 : ReadsCanonical ap0) (hp1 : ReadsCanonical ap1)
    (he : ∀ i q, Array.index_usize extra i=.ok q →
      AspisR1S9ActualPairQMHelperTransportV1.Canonical q)
    (hp : ReadsCanonical parts)
    (hproducer : weights.factored_s2_libra_weights ap0 ap1 extra=.ok libra)
    (hactive : weights.Weights.pair_loop8 {start:=0#usize,«end»:=4#usize}
      f parts libra=.ok out) : ReadsCanonical out := by
  have hl := (AspisR1S9ActualPairHelperLoopToOldV1.actual_helper_success_to_old
    ap0 ap1 extra libra hp0 hp1 he hproducer).1
  exact AspisR1S9ActiveFourCanonicalV1.active_loop_success_canonical
    f libra {start:=0#usize,«end»:=4#usize} parts out hp hl hactive
#print axioms factored_active_success_canonical
end AspisR1S9FactoredActiveCanonicalV1
