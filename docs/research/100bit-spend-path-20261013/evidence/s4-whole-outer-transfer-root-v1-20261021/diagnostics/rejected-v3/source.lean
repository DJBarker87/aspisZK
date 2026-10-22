import S4WholeHelperTransferRootV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1FastDotsWholeOuterTransferRootV1
open AspisR1FastDotsCurrent
open AspisR1FromFnP6Generated
open AspisR1FromFnP6 (statefulFromFnRun)
abbrev Ops := FourDotsOps
abbrev Wide := aspis_core.field.wide_exact.WideExact
abbrev Capture := Array U8 608#usize × Array Wide 29#usize
abbrev OuterFn := fast_dots.four_dots.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact
abbrev install := AspisR1FastDotsFourCallbacksForwardRootV1.install

private theorem bind_ok_inv {A B : Type} {r : Result A} {f : A → Result B} {x : B}
    (h : (r >>= f)=.ok x) : ∃ a, r=.ok a ∧ f a=.ok x := by
  cases r with
  | ok a => exact ⟨a,rfl,h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

/-- Four ordered callbacks with unchanged capture build the exact literal
array in the retained P6 constructor. No independent constructor success. -/
theorem p6_four_of_literal_callbacks
    (ops : Ops) (c : Capture) (v0 v1 v2 v3 : Wide)
    (h0 : (OuterFn ops).call_mut c 0#usize=.ok (v0,c))
    (h1 : (OuterFn ops).call_mut c 1#usize=.ok (v1,c))
    (h2 : (OuterFn ops).call_mut c 2#usize=.ok (v2,c))
    (h3 : (OuterFn ops).call_mut c 3#usize=.ok (v3,c)) :
    arrayFromFnP6 4#usize (OuterFn ops) c =
      .ok (Array.make 4#usize [v0,v1,v2,v3]) := by
  have hs0 : fnMutStep (OuterFn ops) (c,0#usize) 0 =
      .ok (v0,(c,1#usize)) := by
    change (do
      let (value,st) ← (OuterFn ops).call_mut c 0#usize
      let next ← 0#usize + 1#usize
      .ok (value,(st,next)))=.ok (v0,(c,1#usize))
    rw [h0,bind_tc_ok]
    change (do let next ← 0#usize + 1#usize; .ok (v0,(c,next)))=.ok (v0,(c,1#usize))
    have hadd : (0#usize + 1#usize : Result Usize)=.ok 1#usize := by decide
    rw [hadd,bind_tc_ok]
  have hs1 : fnMutStep (OuterFn ops) (c,1#usize) 1 =
      .ok (v1,(c,2#usize)) := by
    change (do
      let (value,st) ← (OuterFn ops).call_mut c 1#usize
      let next ← 1#usize + 1#usize
      .ok (value,(st,next)))=.ok (v1,(c,2#usize))
    rw [h1,bind_tc_ok]
    change (do let next ← 1#usize + 1#usize; .ok (v1,(c,next)))=.ok (v1,(c,2#usize))
    have hadd : (1#usize + 1#usize : Result Usize)=.ok 2#usize := by decide
    rw [hadd,bind_tc_ok]
  have hs2 : fnMutStep (OuterFn ops) (c,2#usize) 2 =
      .ok (v2,(c,3#usize)) := by
    change (do
      let (value,st) ← (OuterFn ops).call_mut c 2#usize
      let next ← 2#usize + 1#usize
      .ok (value,(st,next)))=.ok (v2,(c,3#usize))
    rw [h2,bind_tc_ok]
    change (do let next ← 2#usize + 1#usize; .ok (v2,(c,next)))=.ok (v2,(c,3#usize))
    have hadd : (2#usize + 1#usize : Result Usize)=.ok 3#usize := by decide
    rw [hadd,bind_tc_ok]
  have hs3 : fnMutStep (OuterFn ops) (c,3#usize) 3 =
      .ok (v3,(c,4#usize)) := by
    change (do
      let (value,st) ← (OuterFn ops).call_mut c 3#usize
      let next ← 3#usize + 1#usize
      .ok (value,(st,next)))=.ok (v3,(c,4#usize))
    rw [h3,bind_tc_ok]
    change (do let next ← 3#usize + 1#usize; .ok (v3,(c,next)))=.ok (v3,(c,4#usize))
    have hadd : (3#usize + 1#usize : Result Usize)=.ok 4#usize := by decide
    rw [hadd,bind_tc_ok]
  have htrace : AspisR1FromFnP6.StatefulFromFnTrace (fnMutStep (OuterFn ops))
      4 0 (c,0#usize) [v0,v1,v2,v3] (c,4#usize) :=
    .call hs0 (.call hs1 (.call hs2 (.call hs3 (.done _ _))))
  have hrun := (AspisR1FromFnP6.statefulFromFnRun_success_iff_trace
    (fnMutStep (OuterFn ops)) 4 0 (c,0#usize) [v0,v1,v2,v3] (c,4#usize)).mpr htrace
  unfold arrayFromFnP6 core.array.from_fn_model core.array.from_fn_trace_model
  change (do
    let (values,last) ← packArrayState 4#usize
      (statefulFromFnRun (fnMutStep (OuterFn ops)) 4 0 (c,0#usize))
    .ok values)=.ok (Array.make 4#usize [v0,v1,v2,v3])
  rw [hrun]
  rfl

/-- The complete selected fixed-call four-dot function transfers to the
original generated P6 function on exactly the same input and returned array. -/
theorem installed_fixed_four_success_old_four
    (base : Ops) (q : Slice U8) (g : Array Wide 29#usize) (out : Array Wide 4#usize)
    (hfixed : fast_dots.four_dots_fixed (install base) q g=.ok out) :
    fast_dots.four_dots (install base) q g=.ok out := by
  unfold fast_dots.four_dots_fixed at hfixed
  obtain ⟨s,hs,hfixed⟩ := bind_ok_inv hfixed
  obtain ⟨r,hr,hfixed⟩ := bind_ok_inv hfixed
  obtain ⟨opening,hprefix,hfixed⟩ := bind_ok_inv hfixed
  obtain ⟨v0,h0,hfixed⟩ := bind_ok_inv hfixed
  obtain ⟨v1,h1,hfixed⟩ := bind_ok_inv hfixed
  obtain ⟨v2,h2,hfixed⟩ := bind_ok_inv hfixed
  obtain ⟨v3,h3,hfixed⟩ := bind_ok_inv hfixed
  have hc0 := AspisR1FastDotsWholeHelperTransferRootV1.installed_fixed_helper_success_old_callback
    base opening g 0#usize v0 h0
  have hc1 := AspisR1FastDotsWholeHelperTransferRootV1.installed_fixed_helper_success_old_callback
    base opening g 1#usize v1 h1
  have hc2 := AspisR1FastDotsWholeHelperTransferRootV1.installed_fixed_helper_success_old_callback
    base opening g 2#usize v2 h2
  have hc3 := AspisR1FastDotsWholeHelperTransferRootV1.installed_fixed_helper_success_old_callback
    base opening g 3#usize v3 h3
  have hp6 := p6_four_of_literal_callbacks (install base) (opening,g) v0 v1 v2 v3 hc0 hc1 hc2 hc3
  have harray : (install base).arrayFromFn 4#usize (OuterFn (install base)) (opening,g)=.ok out := by
    change arrayFromFnP6 4#usize (OuterFn (install base)) (opening,g)=.ok out
    exact hp6.trans hfixed
  unfold fast_dots.four_dots
  simp only [hs,hr,hprefix,bind_tc_ok]
  exact harray

#print axioms p6_four_of_literal_callbacks
#print axioms installed_fixed_four_success_old_four
end AspisR1FastDotsWholeOuterTransferRootV1
