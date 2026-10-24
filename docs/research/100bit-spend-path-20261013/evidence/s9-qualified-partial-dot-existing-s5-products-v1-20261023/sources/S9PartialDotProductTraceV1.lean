import S9NativePushNewProductV1
import S9PartialDotReaderDomainV1
import S9PartialHighFinishReachedV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
open AspisR1S9ProductionPairCutV1
namespace AspisR1S9PartialDotProductTraceV1
open AspisR1S9PartialHighFinishReachedV1 (W Q Dot Iter)
open AspisR1S9PartialDotReaderDomainV1 (index index_exact index_maps_s5_reader)
open AspisR1S9NativeFieldS5BoundedReaderV1 (toS5)
open AspisR1S9NativePushProductSumV1
open AspisR1S9NativePushNewProductV1
open AspisR1S9ActualEbyKBackendTransportV1
open AspisR1FastDotsPushProductTraceRootV1
open AspisR1FastDotsTailFieldProductRootV1
abbrev Common := Array Q 16#usize
abbrev State := Iter × Dot
abbrev Outcome := core.result.Result W verifier.Error
private theorem bind_success {A B : Type} (m : Result A) (next : A → Result B) (out : B)
    (h : (do let x ← m; next x)=.ok out) : ∃ x,m=.ok x ∧ next x=.ok out := by
  cases m with
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h
  | ok x => exact ⟨x,rfl,h⟩

private theorem cont_calls (f : Slice U8) (common : Common) (s : Usize)
    (it it1 : Iter) (dot dot1 : Dot)
    (h : weights.partial_dot_loop.body f common s it dot=.ok (.cont (it1,dot1))) :
    ∃ j w q,
      core.iter.range.IteratorRange.next core.iter.range.StepUsize it=.ok (some j,it1) ∧
      weights.field f (index s j)=.ok w ∧ Array.index_usize common j=.ok q ∧
      fast_pairing.EbyKDot.push dot w q=.ok (.Ok (),dot1) := by
  unfold weights.partial_dot_loop.body at h
  obtain ⟨next,hn,h⟩ := bind_success _ _ _ h
  rcases next with ⟨o,itNext⟩
  cases o with
  | none => obtain ⟨value,hf,h⟩ := bind_success _ _ _ h; cases h
  | some j =>
    simp only [lift,bind_tc_ok] at h
    obtain ⟨w,hw,h⟩ := bind_success _ _ _ h
    obtain ⟨q,hq,h⟩ := bind_success _ _ _ h
    obtain ⟨p,hp,h⟩ := bind_success _ _ _ h
    rcases p with ⟨r,d⟩
    cases r with
    | Err e => cases h
    | Ok u =>
      cases u
      have he : (itNext,d)=(it1,dot1) := ControlFlow.cont.inj (Result.ok.inj h)
      have hi : itNext=it1 := congrArg Prod.fst he
      have hd : d=dot1 := congrArg Prod.snd he
      subst itNext; subst d
      exact ⟨j,w,q,hn,hw,hq,hp⟩

private theorem done_same_finish (f : Slice U8) (common : Common) (s : Usize)
    (it : Iter) (dot : Dot) (out : W)
    (h : weights.partial_dot_loop.body f common s it dot=.ok (.done (.Ok out))) :
    ∃ it1,core.iter.range.IteratorRange.next core.iter.range.StepUsize it=.ok (none,it1) ∧
      fast_pairing.EbyKDot.finish dot=.ok out := by
  unfold weights.partial_dot_loop.body at h
  obtain ⟨next,hn,h⟩ := bind_success _ _ _ h
  rcases next with ⟨o,it1⟩
  cases o with
  | none =>
    obtain ⟨value,hf,h⟩ := bind_success _ _ _ h
    have he : value=out := core.result.Result.Ok.inj (ControlFlow.done.inj (Result.ok.inj h))
    subst value
    exact ⟨it1,hn,hf⟩
  | some j =>
    simp only [lift,bind_tc_ok] at h
    obtain ⟨w,hw,h⟩ := bind_success _ _ _ h
    obtain ⟨q,hq,h⟩ := bind_success _ _ _ h
    obtain ⟨p,hp,h⟩ := bind_success _ _ _ h
    rcases p with ⟨r,d⟩
    cases r with
    | Err e => cases h
    | Ok u => cases u; cases h

private theorem none_stopped (it it1 : Iter)
    (hn : core.iter.range.IteratorRange.next core.iter.range.StepUsize it=.ok (none,it1)) :
    it.end.val ≤ it.start.val := by
  have hs := core.iter.range.IteratorRange.next_UScalar_spec
    (cloneInst:=core.clone.CloneUsize) (partialOrdInst:=core.cmp.PartialOrdUsize)
    (by intros; rfl) (by intros; rfl) it
  rw [hn,WP.spec_ok] at hs
  by_cases hlt : it.start.val < it.end.val
  · simp only [hlt,↓reduceIte] at hs
    rcases hs with ⟨⟨ho,_⟩,_⟩
    cases ho
  · omega

private theorem loop_cases {A B : Type} (step : A → Result (ControlFlow A B)) (s : A) (out : B)
    (h : Aeneas.Std.loop step s=.ok out) :
    step s=.ok (.done out) ∨ ∃ t,step s=.ok (.cont t) ∧ Aeneas.Std.loop step t=.ok out := by
  rw [Aeneas.Std.loop.eq_def] at h
  cases hs : step s with
  | fail e => rw [hs] at h; cases h
  | div => rw [hs] at h; cases h
  | ok flow =>
    rw [hs] at h
    cases flow with
    | done value =>
      change Result.ok value=Result.ok out at h
      have he := Result.ok.inj h
      subst value
      exact Or.inl rfl
    | cont t => exact Or.inr ⟨t,rfl,h⟩

/-- Complete partial-loop trace with ONE joint final native accumulator and
its SAME finish call. This theorem is at the qualified cut's explicitly bound
Q.raw interpretation; actual Rust raw refinement remains separate. -/
theorem actual_partial_loop_source_trace
    (f : Slice U8) (common : Common) (s : Usize) (hs : s.val < 4)
    (it : Iter) (dot : Dot) (out : W)
    (hdiv : (Slice.len f /32#usize : Result Usize)=.ok (64#usize))
    (hend : it.end.val=16) (hstart : it.start.val ≤ 16)
    (hrun : weights.partial_dot_loop it f common s dot=.ok (.Ok out)) :
    ∃ (js : List Usize) (xs : Inputs) (final : Dot),
      AspisR1DotCountBoundV1.AcceptedPushTrace AspisR1EbyKPushDecodedProductUpdate.QRaw
        (toSourceState dot) xs (toSourceState final) ∧
      fast_pairing.EbyKDot.finish final=.ok out ∧
      (∀ p ∈ xs,AspisR1EbyKPowerValueCanonicalToPush.pushCanonical p.1) ∧
      List.Forall₂ (fun j p => ∃ w q,
        weights.field f (index s j)=.ok w ∧ Array.index_usize common j=.ok q ∧
        p=(toSourceWide w,toSourceQ q)) js xs ∧
      js.length=16-it.start.val := by
  let step : State → Result (ControlFlow State Outcome) :=
    fun p => weights.partial_dot_loop.body f common s p.1 p.2
  have hloop : Aeneas.Std.loop step (it,dot)=.ok (.Ok out) := hrun
  induction hfuel : 16-it.start.val generalizing it dot with
  | zero =>
    rcases loop_cases step (it,dot) (.Ok out) hloop with hd | ⟨next,hc,ht⟩
    · obtain ⟨it1,hn,hf⟩ := done_same_finish f common s it dot out hd
      exact ⟨[],[],dot,AspisR1DotCountBoundV1.AcceptedPushTrace.nil _,hf,by simp,List.Forall₂.nil,by simp⟩
    · rcases next with ⟨it1,dot1⟩
      obtain ⟨j,w,q,hn,hw,hq,hp⟩ := cont_calls f common s it it1 dot dot1 hc
      obtain ⟨hj,hlt,hstep,he⟩ := AspisR1S9ActualDotRangeBoundsV1.range_next_index_bounds it it1 j hn
      have hv : j.val=it.start.val := congrArg (fun x : Usize => x.val) hj
      omega
  | succ fuel ih =>
    rcases loop_cases step (it,dot) (.Ok out) hloop with hd | ⟨next,hc,ht⟩
    · obtain ⟨it1,hn,hf⟩ := done_same_finish f common s it dot out hd
      have hstop := none_stopped it it1 hn
      exact ⟨[],[],dot,AspisR1DotCountBoundV1.AcceptedPushTrace.nil _,hf,by simp,List.Forall₂.nil,by simp;omega⟩
    · rcases next with ⟨it1,dot1⟩
      obtain ⟨j,w,q,hn,hw,hq,hp⟩ := cont_calls f common s it it1 dot dot1 hc
      obtain ⟨hj,hlt,hstep,he⟩ := AspisR1S9ActualDotRangeBoundsV1.range_next_index_bounds it it1 j hn
      have hend1 : it1.end.val=16 := by rw [he];exact hend
      have hstart1 : it1.start.val ≤ 16 := by
        have hv : j.val=it.start.val := congrArg (fun x : Usize => x.val) hj
        omega
      have hfuel1 : 16-it1.start.val=fuel := by omega
      have hrun1 : weights.partial_dot_loop it1 f common s dot1=.ok (.Ok out) := ht
      obtain ⟨js,xs,final,htrace,hfinish,hcanonical,hcorr,hlen⟩ :=
        ih it1 dot1 hend1 hstart1 hrun1 ht hfuel1
      have hj16 : j.val < 16 := by omega
      have hm := index_maps_s5_reader f s j hs hj16 hdiv
      rw [hw] at hm
      have hr := hm.symm
      rw [AspisR1S5PairCutTransparentReaderV1.actualReader_eq_checkedCallback] at hr
      have hcan := AspisR1S5PairCutFieldCallbackV1.checkedFieldCallback_success_push_canonical
        f (index s j) (toS5 w) hr
      rw [native_reader_value_to_source] at hcan
      have hpush := AspisR1S9ActualEbyKRawAliasV1.actual_push_success_s5_backend dot dot1 w q hp
      refine ⟨j::js,(toSourceWide w,toSourceQ q)::xs,final,
        AspisR1DotCountBoundV1.AcceptedPushTrace.cons _ _ _ _ _ _ hpush htrace,
        hfinish,?_,List.Forall₂.cons ⟨w,q,hw,hq,rfl⟩ hcorr,?_⟩
      · intro p hm
        simp only [List.mem_cons] at hm
        rcases hm with he | hm
        · cases he;exact hcan
        · exact hcanonical p hm
      · simp only [List.length_cons];omega

/-- SAME actual partial wrapper supplies its own initial zero state; existing
product mathematics then fixes the final accumulator value, jointly with the
actual finish output and ordered source operands. No history/data Can input. -/
theorem actual_partial_source_product_sum
    (f : Slice U8) (common : Common) (s : Usize) (hs : s.val < 4) (out : W)
    (hdiv : (Slice.len f /32#usize : Result Usize)=.ok (64#usize))
    (hrun : weights.partial_dot f common s=.ok (.Ok out)) :
    ∃ (js : List Usize) (xs : Inputs) (final : Dot),
      fast_pairing.EbyKDot.finish final=.ok out ∧ js.length=16 ∧
      List.Forall₂ (fun j p => ∃ w q,
        weights.field f (index s j)=.ok w ∧ Array.index_usize common j=.ok q ∧
        p=(toSourceWide w,toSourceQ q)) js xs ∧
      decodeState (stateValue (toSourceState final))=productSum xs := by
  unfold weights.partial_dot at hrun
  obtain ⟨dot,hnew,hrun⟩ := bind_success _ _ _ hrun
  obtain ⟨js,xs,final,htrace,hfinish,hcanonical,hcorr,hlen⟩ :=
    actual_partial_loop_source_trace f common s hs {start:=0#usize,«end»:=16#usize} dot out
      hdiv rfl (by decide) hrun
  have hz := native_new_source_zero dot hnew
  have hi := source_zero_invariants
  have h0 : AspisR1DotCountBoundV1.sumsBelowCount (toSourceState dot).count.val (toSourceState dot).c0.sums := by
    rw [hz];exact hi.1
  have h1 : AspisR1DotCountBoundV1.sumsBelowCount (toSourceState dot).count.val (toSourceState dot).c1.sums := by
    rw [hz];exact hi.2
  have hp := accepted_trace_product_sum (toSourceState dot) (toSourceState final) xs h0 h1 hcanonical htrace
  have hd := decode_product_fold xs (stateValue (toSourceState dot))
  rw [←hp,hz,decode_zero_state,zero_add] at hd
  exact ⟨js,xs,final,hfinish,by simpa using hlen,hcorr,hd⟩

#print axioms actual_partial_loop_source_trace
#print axioms actual_partial_source_product_sum
end AspisR1S9PartialDotProductTraceV1
