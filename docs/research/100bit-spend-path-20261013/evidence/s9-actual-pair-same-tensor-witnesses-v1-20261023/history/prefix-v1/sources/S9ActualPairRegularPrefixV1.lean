import S9ActualRegularKindsTraceV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open AspisR1S9ProductionPairCutV1
namespace AspisR1S9ActualPairRegularPrefixV1
open AspisR1S9ActualProcessKindTensorReachedV1
variable [allocation : AspisR1S9AllocationInterfaceV1.Allocation]
private theorem bind_success {A B : Type} (m : Result A) (next : A → Result B) (out : B)
    (h : (do let x ← m; next x)=.ok out) : ∃ x, m=.ok x ∧ next x=.ok out := by
  cases m with
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h
  | ok x => exact ⟨x,rfl,h⟩

/-- The actual accepted Pair supplies its SAME regular-kinds call, powers,
allocated scratch, n/length guard and shared decision. No later helper or
self1 state is substituted for the original receiver. -/
theorem actual_pair_success_regular_prefix
    (self : weights.Weights) (alpha : Slice W) (f : Slice U8) (kappa out : W)
    (hfold : Slice.len alpha=2#usize)
    (h : weights.Weights.pair self alpha f kappa=.ok (.Ok out)) :
    ∃ (n expectedN : Usize) (a0 a1 : W) (ap0 ap1 : Powers)
      (scratch scratchOut : Scratch) (shared : Bool) (partsOut : Parts),
      (Slice.len f / 32#usize)=.ok n ∧
      weights.Weights.pair_loop0 {start:=0#usize,«end»:=2#usize} 1024#usize=.ok expectedN ∧
      (n != expectedN)=false ∧
      Slice.index_usize alpha 0#usize=.ok a0 ∧ weights.powers 4#usize a0=.ok ap0 ∧
      Slice.index_usize alpha 1#usize=.ok a1 ∧ weights.powers 4#usize a1=.ok ap1 ∧
      aspis_core.r0.heap.filled aspis_core.field.QM31.Insts.CoreMarkerCopy n aspis_core.field.QM31.ZERO=.ok (.Ok scratch) ∧
      weights.shared_two_point_guard self 2#usize=.ok shared ∧
      weights.process_regular_kinds self shared alpha f 2#usize n ap0 ap1 scratch
        (Array.repeat 7#usize aspis_core.field.wide_exact.WideExact.ZERO)=.ok (.Ok (),scratchOut,partsOut) := by
  unfold weights.Weights.pair at h
  obtain ⟨n,hn,h⟩ := bind_success _ _ _ h
  obtain ⟨expectedN,hexpected,h⟩ := bind_success _ _ _ h
  cases hparse : (n != expectedN) with
  | true =>
    simp only [hparse,↓reduceIte] at h
    cases h
  | false =>
    simp only [hparse,Bool.false_eq_true,↓reduceIte] at h
    obtain ⟨a0,ha0,h⟩ := bind_success _ _ _ h
    obtain ⟨ap0,hap0,h⟩ := bind_success _ _ _ h
    simp only [hfold,↓reduceIte] at h
    obtain ⟨ap1,hap1producer,h⟩ := bind_success _ _ _ h
    obtain ⟨a1,ha1,hap1⟩ := bind_success _ _ _ hap1producer
    obtain ⟨reserve,hreserve,h⟩ := bind_success _ _ _ h
    cases reserve with
    | Err error => cases h
    | Ok scratch =>
      obtain ⟨shared,hshared,h⟩ := bind_success _ _ _ h
      obtain ⟨processed,hprocessed,h⟩ := bind_success _ _ _ h
      rcases processed with ⟨r,scratchOut,partsOut⟩
      cases r with
      | Err error =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
          core.convert.FromSame.from] at h
        cases h
      | Ok unit =>
        cases unit
        refine ⟨n,expectedN,a0,a1,ap0,ap1,scratch,scratchOut,shared,partsOut,
          hn,?_,hparse,ha0,hap0,ha1,hap1,hreserve,hshared,hprocessed⟩
        simpa only [hfold] using hexpected

#print axioms actual_pair_success_regular_prefix
end AspisR1S9ActualPairRegularPrefixV1
