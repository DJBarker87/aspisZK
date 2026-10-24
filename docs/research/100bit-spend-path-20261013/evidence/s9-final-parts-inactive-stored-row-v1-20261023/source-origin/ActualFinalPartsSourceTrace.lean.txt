import S9ActualPairSharedFinalTraceV1
import S9ActualPairUnsharedFinalTraceV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9FinalPartsSourceTraceV1
open AspisR1S9ProductionPairCutV1
open AspisR1S9ActualProcessKindTensorReachedV1
variable [allocation : AspisR1S9AllocationInterfaceV1.Allocation]
/-- Actual accepted source events only: no canonicality, field meanings or
kappa-polynomial equation is hidden in this trace. The SAME final array and
power array are explicit parameters threaded through the real phase writes. -/
def SharedTrace (self : weights.Weights) (alpha : Slice W) (f : Slice U8) (kappa out : W)
    (partsFinal : Parts) (k : Array W 7#usize) : Prop :=
  Slice.len alpha=2#usize ∧ weights.shared_two_point_guard self 2#usize=.ok true ∧
  weights.Weights.pair self alpha f kappa=.ok (.Ok out) ∧
    ∃ (n : Usize) (a0 a1 : W) (ap0 ap1 : Powers)
      (scratch scratchOut : Scratch) (partsRegular partsShared : Parts)
      (selfCommon : weights.Weights) (common : Array aspis_core.field.QM31 16#usize)
      (partials : Array W 4#usize) (low : Array W 16#usize) (inactive : W)
      (partsInactive : Parts) (useFactored : Bool) (libra : Array W 4#usize),
      (Slice.len f /32#usize : Result Usize)=.ok n ∧ n=64#usize ∧
      Slice.index_usize alpha 0#usize=.ok a0 ∧ weights.powers 4#usize a0=.ok ap0 ∧
      Slice.index_usize alpha 1#usize=.ok a1 ∧ weights.powers 4#usize a1=.ok ap1 ∧
      aspis_core.r0.heap.filled aspis_core.field.QM31.Insts.CoreMarkerCopy n aspis_core.field.QM31.ZERO=.ok (.Ok scratch) ∧
      weights.process_regular_kinds self true alpha f 2#usize n ap0 ap1 scratch
        (Array.repeat 7#usize aspis_core.field.wide_exact.WideExact.ZERO)=.ok (.Ok (),scratchOut,partsRegular) ∧
      weights.Weights.pair_loop1 {start:=0#usize,«end»:=16#usize} self
        (Array.repeat 16#usize aspis_core.field.QM31.ZERO)=.ok (selfCommon,common) ∧
      weights.shared_partials f common=.ok (.Ok partials) ∧
      weights.shared_high partials selfCommon ap0 ap1 partsRegular=.ok (.Ok (),partsShared) ∧
      weights.Weights.pair_loop7 {start:=0#usize,«end»:=16#usize} ap0 ap1
        (Array.repeat 16#usize aspis_core.field.wide_exact.WideExact.ZERO)=.ok low ∧
      weights.grouped_inactive_pair selfCommon f low=.ok inactive ∧
      Array.update partsShared 0#usize inactive=.ok partsInactive ∧
      transport.Variant.Insts.CoreCmpPartialEqVariant.eq selfCommon.variant transport.Variant.S2=.ok useFactored ∧
      (if useFactored then weights.factored_s2_libra_weights ap0 ap1 selfCommon.extra
        else weights.twofold_libra_weights low selfCommon.extra)=.ok libra ∧
      weights.Weights.pair_loop8 {start:=0#usize,«end»:=4#usize} f partsInactive libra=.ok partsFinal ∧
      weights.powers 7#usize kappa=.ok k ∧
      weights.Weights.pair_loop9 {start:=0#usize,«end»:=7#usize} partsFinal k
        aspis_core.field.wide_exact.WideExact.ZERO=.ok out

theorem shared_trace_of_pair
    (self : weights.Weights) (alpha : Slice W) (f : Slice U8) (kappa out : W)
    (hfold : Slice.len alpha=2#usize)
    (hguard : weights.shared_two_point_guard self 2#usize=.ok true)
    (hpair : weights.Weights.pair self alpha f kappa=.ok (.Ok out)) :
    ∃ partsFinal k, SharedTrace self alpha f kappa out partsFinal k := by
  obtain ⟨n,a0,a1,ap0,ap1,scratch,scratchOut,partsRegular,partsShared,selfCommon,common,partials,low,inactive,partsInactive,partsFinal,useFactored,libra,k,hn,hn64,ha0,hap0,ha1,hap1,hreserved,hregular,hcommon,hpartials,hhigh,hlow,hinactive,hpartsInactive,huse,hlibra,hactive,hk,hsum⟩ :=
    AspisR1S9ActualPairSharedFinalTraceV1.actual_pair_success_shared_final_trace self alpha f kappa out hfold hguard hpair
  exact ⟨partsFinal,k,hfold,hguard,hpair,n,a0,a1,ap0,ap1,scratch,scratchOut,partsRegular,partsShared,selfCommon,common,partials,low,inactive,partsInactive,useFactored,libra,hn,hn64,ha0,hap0,ha1,hap1,hreserved,hregular,hcommon,hpartials,hhigh,hlow,hinactive,hpartsInactive,huse,hlibra,hactive,hk,hsum⟩

/-- Actual accepted source events only: no canonicality, field meanings or
kappa-polynomial equation is hidden in this trace. The SAME final array and
power array are explicit parameters threaded through the real phase writes. -/
def UnsharedTrace (self : weights.Weights) (alpha : Slice W) (f : Slice U8) (kappa out : W)
    (partsFinal : Parts) (k : Array W 7#usize) : Prop :=
  Slice.len alpha=2#usize ∧ weights.shared_two_point_guard self 2#usize=.ok false ∧
  weights.Weights.pair self alpha f kappa=.ok (.Ok out) ∧
    ∃ (n : Usize) (a0 a1 : W) (ap0 ap1 : Powers)
      (scratch scratchOut : Scratch) (partsRegular : Parts)
      (low : Array W 16#usize) (inactive : W)
      (partsInactive : Parts) (useFactored : Bool) (libra : Array W 4#usize),
      (Slice.len f /32#usize : Result Usize)=.ok n ∧ n=64#usize ∧
      Slice.index_usize alpha 0#usize=.ok a0 ∧ weights.powers 4#usize a0=.ok ap0 ∧
      Slice.index_usize alpha 1#usize=.ok a1 ∧ weights.powers 4#usize a1=.ok ap1 ∧
      aspis_core.r0.heap.filled aspis_core.field.QM31.Insts.CoreMarkerCopy n aspis_core.field.QM31.ZERO=.ok (.Ok scratch) ∧
      weights.process_regular_kinds self false alpha f 2#usize n ap0 ap1 scratch
        (Array.repeat 7#usize aspis_core.field.wide_exact.WideExact.ZERO)=.ok (.Ok (),scratchOut,partsRegular) ∧
      weights.Weights.pair_loop15 {start:=0#usize,«end»:=16#usize} ap0 ap1
        (Array.repeat 16#usize aspis_core.field.wide_exact.WideExact.ZERO)=.ok low ∧
      weights.grouped_inactive_pair self f low=.ok inactive ∧
      Array.update partsRegular 0#usize inactive=.ok partsInactive ∧
      transport.Variant.Insts.CoreCmpPartialEqVariant.eq self.variant transport.Variant.S2=.ok useFactored ∧
      (if useFactored then weights.factored_s2_libra_weights ap0 ap1 self.extra
        else weights.twofold_libra_weights low self.extra)=.ok libra ∧
      weights.Weights.pair_loop16 {start:=0#usize,«end»:=4#usize} f partsInactive libra=.ok partsFinal ∧
      weights.powers 7#usize kappa=.ok k ∧
      weights.Weights.pair_loop17 {start:=0#usize,«end»:=7#usize} partsFinal k
        aspis_core.field.wide_exact.WideExact.ZERO=.ok out

theorem unshared_trace_of_pair
    (self : weights.Weights) (alpha : Slice W) (f : Slice U8) (kappa out : W)
    (hfold : Slice.len alpha=2#usize)
    (hguard : weights.shared_two_point_guard self 2#usize=.ok false)
    (hpair : weights.Weights.pair self alpha f kappa=.ok (.Ok out)) :
    ∃ partsFinal k, UnsharedTrace self alpha f kappa out partsFinal k := by
  obtain ⟨n,a0,a1,ap0,ap1,scratch,scratchOut,partsRegular,low,inactive,partsInactive,partsFinal,useFactored,libra,k,hn,hn64,ha0,hap0,ha1,hap1,hreserved,hregular,hlow,hinactive,hpartsInactive,huse,hlibra,hactive,hk,hsum⟩ :=
    AspisR1S9ActualPairUnsharedFinalTraceV1.actual_pair_success_unshared_final_trace self alpha f kappa out hfold hguard hpair
  exact ⟨partsFinal,k,hfold,hguard,hpair,n,a0,a1,ap0,ap1,scratch,scratchOut,partsRegular,low,inactive,partsInactive,useFactored,libra,hn,hn64,ha0,hap0,ha1,hap1,hreserved,hregular,hlow,hinactive,hpartsInactive,huse,hlibra,hactive,hk,hsum⟩


def Trace (self : weights.Weights) (alpha : Slice W) (f : Slice U8) (kappa out : W)
    (partsFinal : Parts) (k : Array W 7#usize) : Prop :=
  SharedTrace self alpha f kappa out partsFinal k ∨ UnsharedTrace self alpha f kappa out partsFinal k


#print axioms shared_trace_of_pair
#print axioms unshared_trace_of_pair
end AspisR1S9FinalPartsSourceTraceV1
