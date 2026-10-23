import S9ActualPairRegularPrefixV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open AspisR1S9ProductionPairCutV1
namespace AspisR1S9ActualPairTensorCallsV1
open AspisR1S9ActualProcessKindTensorReachedV1
open AspisR1S9ActualRegularKindsTraceV1
variable [allocation : AspisR1S9AllocationInterfaceV1.Allocation]

def TensorKindCall (self : weights.Weights) (kind : Usize) (alpha : Slice W) (f : Slice U8)
    (folds n : Usize) (ap0 ap1 : Powers) (scratch scratchOut : Scratch) (parts partsOut : Parts) : Prop :=
  KindCall self kind alpha f folds n ap0 ap1 scratch scratchOut parts partsOut ∧
    ∃ tensorOut : Slice Q, weights.Weights.tensor self (rowOfKind kind) folds
      (alloc.vec.Vec.deref_mut scratch).1=.ok tensorOut

def TensorRegularTrace (self : weights.Weights) (shared : Bool) (alpha : Slice W) (f : Slice U8)
    (folds n : Usize) (ap0 ap1 : Powers) (scratch scratchOut : Scratch) (parts partsOut : Parts) : Prop :=
  if shared then
    ∃ (s1 s2 : Scratch) (p1 p2 : Parts),
      TensorKindCall self 2#usize alpha f folds n ap0 ap1 scratch s1 parts p1 ∧
      TensorKindCall self 5#usize alpha f folds n ap0 ap1 s1 s2 p1 p2 ∧
      TensorKindCall self 6#usize alpha f folds n ap0 ap1 s2 scratchOut p2 partsOut
  else
    ∃ (s1 s2 s3 s4 : Scratch) (p1 p2 p3 p4 : Parts),
      TensorKindCall self 1#usize alpha f folds n ap0 ap1 scratch s1 parts p1 ∧
      TensorKindCall self 2#usize alpha f folds n ap0 ap1 s1 s2 p1 p2 ∧
      TensorKindCall self 3#usize alpha f folds n ap0 ap1 s2 s3 p2 p3 ∧
      TensorKindCall self 5#usize alpha f folds n ap0 ap1 s3 s4 p3 p4 ∧
      TensorKindCall self 6#usize alpha f folds n ap0 ap1 s4 scratchOut p4 partsOut

/-- Every recorded source call reaches its tensor on THAT recorded scratch.
S2 proves the D dense branch is unavailable; shared kinds remain2,5,6 only. -/
theorem regular_trace_tensor_calls
    (self : weights.Weights) (shared : Bool) (alpha : Slice W) (f : Slice U8)
    (folds n : Usize) (ap0 ap1 : Powers) (scratch scratchOut : Scratch) (parts partsOut : Parts)
    (hs2 : self.variant=transport.Variant.S2)
    (htrace : RegularTrace self shared alpha f folds n ap0 ap1 scratch scratchOut parts partsOut) :
    TensorRegularTrace self shared alpha f folds n ap0 ap1 scratch scratchOut parts partsOut := by
  have upgrade : ∀ (kind : Usize) (s s' : Scratch) (p p' : Parts),
      KindCall self kind alpha f folds n ap0 ap1 s s' p p' →
      TensorKindCall self kind alpha f folds n ap0 ap1 s s' p p' := by
    intro kind s s' p p' hc
    exact ⟨hc,process_kind_success_reaches_tensor self kind alpha f folds n ap0 ap1 s s' p p' (.Ok ()) hs2 hc⟩
  cases shared with
  | true =>
    obtain ⟨s1,s2,p1,p2,h2,h5,h6⟩ := htrace
    exact ⟨s1,s2,p1,p2,upgrade _ _ _ _ _ h2,upgrade _ _ _ _ _ h5,upgrade _ _ _ _ _ h6⟩
  | false =>
    obtain ⟨s1,s2,s3,s4,p1,p2,p3,p4,h1,h2,h3,h5,h6⟩ := htrace
    exact ⟨s1,s2,s3,s4,p1,p2,p3,p4,upgrade _ _ _ _ _ h1,upgrade _ _ _ _ _ h2,
      upgrade _ _ _ _ _ h3,upgrade _ _ _ _ _ h5,upgrade _ _ _ _ _ h6⟩

/-- Actual accepted native Pair exposes the SAME successful tensors with
actual power producers, allocated scratch, input f, n and shared guard.
No desired tensor/child success is a premise. Both branch traces retain all
real intermediate scratch/parts, and never invent kinds1/3 in a shared run. -/
theorem actual_pair_success_tensor_calls
    (self : weights.Weights) (alpha : Slice W) (f : Slice U8) (kappa out : W)
    (hs2 : self.variant=transport.Variant.S2) (hfold : Slice.len alpha=2#usize)
    (hpair : weights.Weights.pair self alpha f kappa=.ok (.Ok out)) :
    ∃ (n expectedN : Usize) (a0 a1 : W) (ap0 ap1 : Powers)
      (scratch scratchOut : Scratch) (shared : Bool) (partsOut : Parts),
      (Slice.len f / 32#usize : Result Usize)=.ok n ∧
      weights.Weights.pair_loop0 {start:=0#usize,«end»:=2#usize} 1024#usize=.ok expectedN ∧
      (n != expectedN)=false ∧
      Slice.index_usize alpha 0#usize=.ok a0 ∧ weights.powers 4#usize a0=.ok ap0 ∧
      Slice.index_usize alpha 1#usize=.ok a1 ∧ weights.powers 4#usize a1=.ok ap1 ∧
      aspis_core.r0.heap.filled aspis_core.field.QM31.Insts.CoreMarkerCopy n aspis_core.field.QM31.ZERO=.ok (.Ok scratch) ∧
      weights.shared_two_point_guard self 2#usize=.ok shared ∧
      TensorRegularTrace self shared alpha f 2#usize n ap0 ap1 scratch scratchOut
        (Array.repeat 7#usize aspis_core.field.wide_exact.WideExact.ZERO) partsOut := by
  obtain ⟨n,expectedN,a0,a1,ap0,ap1,scratch,scratchOut,shared,partsOut,
      hn,he,hguard,ha0,hap0,ha1,hap1,hfilled,hshared,hregular⟩ :=
    AspisR1S9ActualPairRegularPrefixV1.actual_pair_success_regular_prefix self alpha f kappa out hfold hpair
  have htrace := regular_success_trace self shared alpha f 2#usize n ap0 ap1 scratch scratchOut
    (Array.repeat 7#usize aspis_core.field.wide_exact.WideExact.ZERO) partsOut hregular
  exact ⟨n,expectedN,a0,a1,ap0,ap1,scratch,scratchOut,shared,partsOut,
    hn,he,hguard,ha0,hap0,ha1,hap1,hfilled,hshared,
    regular_trace_tensor_calls self shared alpha f 2#usize n ap0 ap1 scratch scratchOut
      (Array.repeat 7#usize aspis_core.field.wide_exact.WideExact.ZERO) partsOut hs2 htrace⟩

#print axioms regular_trace_tensor_calls
#print axioms actual_pair_success_tensor_calls
end AspisR1S9ActualPairTensorCallsV1
