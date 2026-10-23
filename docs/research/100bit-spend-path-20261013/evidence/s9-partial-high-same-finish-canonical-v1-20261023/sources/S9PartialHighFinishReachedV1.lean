import AspisR1S9ProductionPairCutV1.Funs
import S9ActualDotRangeBoundsV1
import S9LoopInvariantPropertyV1
import S9ActualEbyKFinishCanonicalV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
open AspisR1S9ProductionPairCutV1
namespace AspisR1S9PartialHighFinishReachedV1
abbrev W := aspis_core.field.wide_exact.WideExact
abbrev Q := aspis_core.field.QM31
abbrev Dot := fast_pairing.EbyKDot
abbrev Iter := core.ops.range.Range Usize
abbrev State := Iter × Dot
abbrev Outcome := core.result.Result W verifier.Error
private theorem bind_success {A B : Type} (m : Result A) (next : A → Result B) (out : B)
    (h : (do let x ← m; next x)=.ok out) : ∃ x,m=.ok x ∧ next x=.ok out := by
  cases m with
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h
  | ok x => exact ⟨x,rfl,h⟩

private theorem run_finish (step : State → Result (ControlFlow State Outcome))
    (out : W)
    (hdone : ∀ s,step s=.ok (.done (.Ok out)) → ∃ final,fast_pairing.EbyKDot.finish final=.ok out)
    (hdec : ∀ s t,step s=.ok (.cont t) →
      t.1.end.val-t.1.start.val < s.1.end.val-s.1.start.val)
    (s : State) (hrun : Aeneas.Std.loop step s=.ok (.Ok out)) :
    ∃ final,fast_pairing.EbyKDot.finish final=.ok out := by
  have hpost := AspisR1S9LoopInvariantPropertyV1.loop_invariant_property step
    (fun s => s.1.end.val-s.1.start.val) (fun _ => True)
    (fun r => r=.Ok out → ∃ final,fast_pairing.EbyKDot.finish final=.ok out)
    (by intro s r _ hb he; subst r; exact hdone s hb)
    (by intros; trivial) hdec s (.Ok out) trivial hrun
  exact hpost rfl

private theorem high_done_finish
    (partials : Array W 4#usize) (coeffs : Array Q 4#usize) (it : Iter) (dot : Dot) (out : W)
    (h : weights.high_dot_loop.body partials coeffs it dot=.ok (.done (.Ok out))) :
    ∃ final,fast_pairing.EbyKDot.finish final=.ok out := by
  unfold weights.high_dot_loop.body at h
  obtain ⟨next,hn,h⟩ := bind_success _ _ _ h
  rcases next with ⟨o,it1⟩
  cases o with
  | none =>
    obtain ⟨value,hf,h⟩ := bind_success _ _ _ h
    have he : value=out := core.result.Result.Ok.inj (ControlFlow.done.inj (Result.ok.inj h))
    subst value
    exact ⟨dot,hf⟩
  | some j =>
    obtain ⟨w,hw,h⟩ := bind_success _ _ _ h
    obtain ⟨q,hq,h⟩ := bind_success _ _ _ h
    obtain ⟨p,hp,h⟩ := bind_success _ _ _ h
    rcases p with ⟨r,d⟩
    cases r with
    | Err e => cases h
    | Ok u => cases u; cases h

private theorem high_cont_decrease
    (partials : Array W 4#usize) (coeffs : Array Q 4#usize)
    (it itOut : Iter) (dot dotOut : Dot)
    (h : weights.high_dot_loop.body partials coeffs it dot=.ok (.cont (itOut,dotOut))) :
    itOut.end.val-itOut.start.val < it.end.val-it.start.val := by
  unfold weights.high_dot_loop.body at h
  obtain ⟨next,hn,h⟩ := bind_success _ _ _ h
  rcases next with ⟨o,it1⟩
  cases o with
  | none => obtain ⟨value,hf,h⟩ := bind_success _ _ _ h; cases h
  | some j =>
    obtain ⟨w,hw,h⟩ := bind_success _ _ _ h
    obtain ⟨q,hq,h⟩ := bind_success _ _ _ h
    obtain ⟨p,hp,h⟩ := bind_success _ _ _ h
    rcases p with ⟨r,d⟩
    cases r with
    | Err e => cases h
    | Ok u =>
      cases u
      have he : (it1,d)=(itOut,dotOut) := ControlFlow.cont.inj (Result.ok.inj h)
      have hi : it1=itOut := congrArg Prod.fst he
      obtain ⟨hj,hlt,hs,he⟩ := AspisR1S9ActualDotRangeBoundsV1.range_next_index_bounds it it1 j hn
      have hactive : it.start.val < it.end.val := by simpa only [hj] using hlt
      rw [hi] at hs he
      have heval := congrArg (fun x : Usize => x.val) he
      omega

private theorem partial_done_finish
    (f : Slice U8) (common : Array Q 16#usize) (s : Usize) (it : Iter) (dot : Dot) (out : W)
    (h : weights.partial_dot_loop.body f common s it dot=.ok (.done (.Ok out))) :
    ∃ final,fast_pairing.EbyKDot.finish final=.ok out := by
  unfold weights.partial_dot_loop.body at h
  obtain ⟨next,hn,h⟩ := bind_success _ _ _ h
  rcases next with ⟨o,it1⟩
  cases o with
  | none =>
    obtain ⟨value,hf,h⟩ := bind_success _ _ _ h
    have he : value=out := core.result.Result.Ok.inj (ControlFlow.done.inj (Result.ok.inj h))
    subst value
    exact ⟨dot,hf⟩
  | some j =>
    simp only [lift,bind_tc_ok] at h
    obtain ⟨w,hw,h⟩ := bind_success _ _ _ h
    obtain ⟨q,hq,h⟩ := bind_success _ _ _ h
    obtain ⟨p,hp,h⟩ := bind_success _ _ _ h
    rcases p with ⟨r,d⟩
    cases r with
    | Err e => cases h
    | Ok u => cases u; cases h

private theorem partial_cont_decrease
    (f : Slice U8) (common : Array Q 16#usize) (s : Usize)
    (it itOut : Iter) (dot dotOut : Dot)
    (h : weights.partial_dot_loop.body f common s it dot=.ok (.cont (itOut,dotOut))) :
    itOut.end.val-itOut.start.val < it.end.val-it.start.val := by
  unfold weights.partial_dot_loop.body at h
  obtain ⟨next,hn,h⟩ := bind_success _ _ _ h
  rcases next with ⟨o,it1⟩
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
      have he : (it1,d)=(itOut,dotOut) := ControlFlow.cont.inj (Result.ok.inj h)
      have hi : it1=itOut := congrArg Prod.fst he
      obtain ⟨hj,hlt,hs,he⟩ := AspisR1S9ActualDotRangeBoundsV1.range_next_index_bounds it it1 j hn
      have hactive : it.start.val < it.end.val := by simpa only [hj] using hlt
      rw [hi] at hs he
      have heval := congrArg (fun x : Usize => x.val) he
      omega

/-- SAME actual accepted high loop necessarily reached its own native finish. -/
theorem high_loop_success_finish (partials : Array W 4#usize) (coeffs : Array Q 4#usize)
    (it : Iter) (dot : Dot) (out : W)
    (h : weights.high_dot_loop it partials coeffs dot=.ok (.Ok out)) :
    ∃ final,fast_pairing.EbyKDot.finish final=.ok out := by
  exact run_finish (fun p => weights.high_dot_loop.body partials coeffs p.1 p.2) out
    (fun s hb => high_done_finish partials coeffs s.1 s.2 out hb)
    (fun s t hb => high_cont_decrease partials coeffs s.1 t.1 s.2 t.2 hb) (it,dot) h

/-- SAME actual accepted partial loop necessarily reached its own native finish. -/
theorem partial_loop_success_finish (f : Slice U8) (common : Array Q 16#usize) (s : Usize)
    (it : Iter) (dot : Dot) (out : W)
    (h : weights.partial_dot_loop it f common s dot=.ok (.Ok out)) :
    ∃ final,fast_pairing.EbyKDot.finish final=.ok out := by
  exact run_finish (fun p => weights.partial_dot_loop.body f common s p.1 p.2) out
    (fun s' hb => partial_done_finish f common s s'.1 s'.2 out hb)
    (fun s' t hb => partial_cont_decrease f common s s'.1 t.1 s'.2 t.2 hb) (it,dot) h

theorem actual_high_success_finish (partials : Array W 4#usize) (coeffs : Array Q 4#usize) (out : W)
    (h : weights.high_dot partials coeffs=.ok (.Ok out)) :
    ∃ final,fast_pairing.EbyKDot.finish final=.ok out := by
  unfold weights.high_dot at h
  obtain ⟨dot,hn,h⟩ := bind_success _ _ _ h
  exact high_loop_success_finish partials coeffs _ dot out h

theorem actual_partial_success_finish (f : Slice U8) (common : Array Q 16#usize) (s : Usize) (out : W)
    (h : weights.partial_dot f common s=.ok (.Ok out)) :
    ∃ final,fast_pairing.EbyKDot.finish final=.ok out := by
  unfold weights.partial_dot at h
  obtain ⟨dot,hn,h⟩ := bind_success _ _ _ h
  exact partial_loop_success_finish f common s _ dot out h

theorem actual_high_success_canonical (partials : Array W 4#usize) (coeffs : Array Q 4#usize) (out : W)
    (h : weights.high_dot partials coeffs=.ok (.Ok out)) :
    AspisR1S9ActualPairWideCanonicalV1.Canonical out := by
  obtain ⟨final,hf⟩ := actual_high_success_finish partials coeffs out h
  exact AspisR1S9ActualEbyKFinishCanonicalV1.actual_finish_success_canonical final out hf

theorem actual_partial_success_canonical (f : Slice U8) (common : Array Q 16#usize) (s : Usize) (out : W)
    (h : weights.partial_dot f common s=.ok (.Ok out)) :
    AspisR1S9ActualPairWideCanonicalV1.Canonical out := by
  obtain ⟨final,hf⟩ := actual_partial_success_finish f common s out h
  exact AspisR1S9ActualEbyKFinishCanonicalV1.actual_finish_success_canonical final out hf

#print axioms high_loop_success_finish
#print axioms partial_loop_success_finish
#print axioms actual_high_success_finish
#print axioms actual_partial_success_finish
#print axioms actual_high_success_canonical
#print axioms actual_partial_success_canonical
end AspisR1S9PartialHighFinishReachedV1
