import S9ActualPairRegularPrefixV1
import S9ActualPairQuotient64V1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open AspisR1S9ProductionPairCutV1
namespace AspisR1S9ActualPairUnsharedFinalTraceV1
open AspisR1S9ActualProcessKindTensorReachedV1
variable [allocation : AspisR1S9AllocationInterfaceV1.Allocation]
private theorem bind_success {A B : Type} (m : Result A) (next : A → Result B) (out : B)
    (h : (do let x ← m; next x)=.ok out) : ∃ x,m=.ok x ∧ next x=.ok out := by
  cases m with
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h
  | ok x => exact ⟨x,rfl,h⟩

/-- One accepted unshared two-fold Pair supplies its complete ordered source
trace through the actual returned final sum. No child success or intermediate
array is supplied as a premise. Other branch behavior is not claimed. -/
theorem actual_pair_success_unshared_final_trace
    (self : weights.Weights) (alpha : Slice W) (f : Slice U8) (kappa out : W)
    (hfold : Slice.len alpha=2#usize)
    (hguard : weights.shared_two_point_guard self 2#usize=.ok false)
    (h : weights.Weights.pair self alpha f kappa=.ok (.Ok out)) :
    ∃ (n : Usize) (a0 a1 : W) (ap0 ap1 : Powers)
      (scratch scratchOut : Scratch) (partsRegular : Parts)
      (low : Array W 16#usize) (inactive : W)
      (partsInactive partsFinal : Parts) (useFactored : Bool) (libra : Array W 4#usize)
      (k : Array W 7#usize),
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
        aspis_core.field.wide_exact.WideExact.ZERO=.ok out := by
  have hquot := AspisR1S9ActualPairQuotient64V1.actual_pair_success_quotient64 self alpha f kappa out hfold h
  unfold weights.Weights.pair at h
  obtain ⟨n,hn,h⟩ := bind_success _ _ _ h
  have hn64 : n=64#usize := Result.ok.inj (hn.symm.trans hquot)
  obtain ⟨expectedN,he,h⟩ := bind_success _ _ _ h
  cases hg : (n != expectedN) with
  | true => simp only [hg,↓reduceIte] at h; cases h
  | false =>
    simp only [hg,Bool.false_eq_true,↓reduceIte] at h
    obtain ⟨a0,ha0,h⟩ := bind_success _ _ _ h
    obtain ⟨ap0,hap0,h⟩ := bind_success _ _ _ h
    simp only [hfold,↓reduceIte] at h
    obtain ⟨ap1,hap1producer,h⟩ := bind_success _ _ _ h
    obtain ⟨a1,ha1,hap1⟩ := bind_success _ _ _ hap1producer
    obtain ⟨reserved,hreserved,h⟩ := bind_success _ _ _ h
    cases reserved with
    | Err e => cases h
    | Ok scratch =>
      obtain ⟨shared,hshared,h⟩ := bind_success _ _ _ h
      have hshared' : shared=false := Result.ok.inj (hshared.symm.trans hguard)
      subst shared
      obtain ⟨processed,hprocessed,h⟩ := bind_success _ _ _ h
      rcases processed with ⟨r,scratchOut,partsRegular⟩
      cases r with
      | Err e =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
          core.convert.FromSame.from] at h
        cases h
      | Ok u =>
        cases u
        obtain ⟨cf,hcf,h⟩ := bind_success
          (core.result.Result.Insts.CoreOpsTry.branch (E:=verifier.Error) (.Ok ())) _ _ h
        have hcfEq : cf=core.ops.control_flow.ControlFlow.Continue () := (Result.ok.inj hcf).symm
        cases hcfEq
        simp only [↓reduceIte] at h
        simp only [hfold,↓reduceIte] at h
        obtain ⟨low,hlow,h⟩ := bind_success _ _ _ h
        obtain ⟨inactive,hinactive,h⟩ := bind_success _ _ _ h
        obtain ⟨partsInactive,hpartsInactive,h⟩ := bind_success _ _ _ h
        obtain ⟨useFactored,huse,h⟩ := bind_success _ _ _ h
        obtain ⟨libra,hlibra,h⟩ := bind_success _ _ _ h
        obtain ⟨partsFinal,hpartsFinal,h⟩ := bind_success _ _ _ h
        obtain ⟨k,hk,h⟩ := bind_success _ _ _ h
        obtain ⟨sum,hsum,h⟩ := bind_success _ _ _ h
        have he : sum=out := core.result.Result.Ok.inj (Result.ok.inj h)
        subst sum
        exact ⟨n,a0,a1,ap0,ap1,scratch,scratchOut,partsRegular,
          low,inactive,partsInactive,partsFinal,useFactored,libra,k,
          hn,hn64,ha0,hap0,ha1,hap1,hreserved,hprocessed,
          hlow,hinactive,hpartsInactive,huse,hlibra,hpartsFinal,hk,hsum⟩

#print axioms actual_pair_success_unshared_final_trace
end AspisR1S9ActualPairUnsharedFinalTraceV1
