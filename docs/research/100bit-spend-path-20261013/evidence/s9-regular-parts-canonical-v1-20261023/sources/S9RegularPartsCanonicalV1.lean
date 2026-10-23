import S9ProcessKindPartsCanonicalV1
import S9ActualRegularKindsTraceV1
import S9ActualPairInitialWeightsV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9RegularPartsCanonicalV1
open AspisR1S9ProductionPairCutV1
open AspisR1S9ActualProcessKindTensorReachedV1
open AspisR1S9ActualRegularKindsTraceV1
open AspisR1S9ActualFinalSumV1
abbrev W := aspis_core.field.wide_exact.WideExact
variable [allocation : AspisR1S9AllocationInterfaceV1.Allocation]

theorem initial_parts_good : Good (Array.repeat 7#usize aspis_core.field.wide_exact.WideExact.ZERO) :=
  AspisR1S9ActualPairInitialWeightsV1.repeated_native_reads
    AspisR1S9ActualPairWideCanonicalV1.Canonical 7#usize _
      AspisR1S9ActualPairWideOutputCanonicalV1.zero_canonical

/-- All real regular kind calls preserve parts canonicality, starting from
any canonical parts. Source trace supplies its own actual3/5 child successes. -/
theorem regular_success_preserves_good
    (self : weights.Weights) (shared : Bool) (alpha : Slice W) (f : Slice U8)
    (n : Usize) (ap0 ap1 : Powers) (scratch scratchOut : Scratch) (parts partsOut : Parts)
    (hs2 : self.variant=transport.Variant.S2)
    (hp0 : AspisR1S9ActualPairScalarCallbackV1.GoodArray ap0)
    (hp1 : AspisR1S9ActualPairScalarCallbackV1.GoodArray ap1)
    (hparts : Good parts)
    (hcall : weights.process_regular_kinds self shared alpha f 2#usize n ap0 ap1 scratch parts=
      .ok (.Ok (),scratchOut,partsOut)) : Good partsOut := by
  have ht := regular_success_trace self shared alpha f 2#usize n ap0 ap1 scratch scratchOut parts partsOut hcall
  have upgrade : ∀ (kind : Usize), kind.val<7 →
      ∀ (s s' : Scratch) (p p' : Parts), Good p →
        KindCall self kind alpha f 2#usize n ap0 ap1 s s' p p' → Good p' := by
    intro kind hk s s' p p' hp hc
    exact AspisR1S9ProcessKindPartsCanonicalV1.process_kind_success_preserves_good
      self kind alpha f n ap0 ap1 s s' p p' hs2 hk hp0 hp1 hp hc
  cases shared with
  | true =>
    obtain ⟨s1,s2,p1,p2,c2,c5,c6⟩ := ht
    have h1 := upgrade 2#usize (by decide) scratch s1 parts p1 hparts c2
    have h2 := upgrade 5#usize (by decide) s1 s2 p1 p2 h1 c5
    exact upgrade 6#usize (by decide) s2 scratchOut p2 partsOut h2 c6
  | false =>
    obtain ⟨s1,s2,s3,s4,p1,p2,p3,p4,c1,c2,c3,c5,c6⟩ := ht
    have h1 := upgrade 1#usize (by decide) scratch s1 parts p1 hparts c1
    have h2 := upgrade 2#usize (by decide) s1 s2 p1 p2 h1 c2
    have h3 := upgrade 3#usize (by decide) s2 s3 p2 p3 h2 c3
    have h4 := upgrade 5#usize (by decide) s3 s4 p3 p4 h3 c5
    exact upgrade 6#usize (by decide) s4 scratchOut p4 partsOut h4 c6

theorem regular_from_zero_success_good
    (self : weights.Weights) (shared : Bool) (alpha : Slice W) (f : Slice U8)
    (n : Usize) (ap0 ap1 : Powers) (scratch scratchOut : Scratch) (partsOut : Parts)
    (hs2 : self.variant=transport.Variant.S2)
    (hp0 : AspisR1S9ActualPairScalarCallbackV1.GoodArray ap0)
    (hp1 : AspisR1S9ActualPairScalarCallbackV1.GoodArray ap1)
    (hcall : weights.process_regular_kinds self shared alpha f 2#usize n ap0 ap1 scratch
      (Array.repeat 7#usize aspis_core.field.wide_exact.WideExact.ZERO)=.ok (.Ok (),scratchOut,partsOut)) :
    Good partsOut :=
  regular_success_preserves_good self shared alpha f n ap0 ap1 scratch scratchOut _ partsOut
    hs2 hp0 hp1 initial_parts_good hcall

#print axioms initial_parts_good
#print axioms regular_success_preserves_good
#print axioms regular_from_zero_success_good
end AspisR1S9RegularPartsCanonicalV1
