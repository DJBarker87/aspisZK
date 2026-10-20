import CurrentClaimRangeStep
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1CurrentPreparedClaim.ClaimTrace
open Concrete
private theorem loop_success_cases {α β : Type} (step : α → Result (ControlFlow α β))
    (state : α) (out : β) (h : Aeneas.Std.loop step state=Result.ok out) :
    step state=Result.ok (ControlFlow.done out) ∨
      ∃ stateNext, step state=Result.ok (ControlFlow.cont stateNext) ∧
        Aeneas.Std.loop step stateNext=Result.ok out := by
  rw [Aeneas.Std.loop.eq_def] at h
  cases hs : step state with
  | fail e => simp [hs] at h
  | div => simp [hs] at h
  | ok cf =>
    cases cf with
    | done result => simp [hs] at h; subst result; exact Or.inl rfl
    | cont stateNext => simp [hs] at h; exact Or.inr ⟨stateNext,rfl,h⟩

inductive Chain {D H : Type} (ops : ClaimDotOps D) (inst : aspis_core.Digest32 H)
    (sem : r1_semantic.Verified H) (y1 : Slice U8) (g : Array E 29#usize)
    (k : Array E 7#usize) : Range → Array E 7#usize → E → Prop
  | done (iter : Range) (parts : Array E 7#usize) (out : E)
      (atEnd : iter.start.val=6) (sum : verifier.prepared_claim_sum k parts=Result.ok out) :
      Chain ops inst sem y1 g k iter parts out
  | step {iter iter' : Range} {parts parts' : Array E 7#usize} {out : E}
      (point i : Usize) (value : E)
      (next : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter=Result.ok (some point,iter'))
      (dot : verifier.prepared_claim_dot ops inst sem y1 g point=Result.ok (core.result.Result.Ok value))
      (increment : (point+1#usize : Result Usize)=Result.ok i)
      (write : Array.update parts i value=Result.ok parts')
      (tail : Chain ops inst sem y1 g k iter' parts' out) :
      Chain ops inst sem y1 g k iter parts out

theorem successful_loop_has_chain {D H : Type} (ops : ClaimDotOps D) (inst : aspis_core.Digest32 H)
    (sem : r1_semantic.Verified H) (y1 : Slice U8) (g : Array E 29#usize)
    (k parts : Array E 7#usize) (iter : Range) (out : E)
    (hend : iter.end.val=6) (hi : iter.start.val≤6)
    (hrun : verifier.prepared_claim_loop ops inst iter sem y1 g k parts=Result.ok (core.result.Result.Ok out)) :
    Chain ops inst sem y1 g k iter parts out := by
  let step := fun s : Range × Array E 7#usize => verifier.prepared_claim_loop.body ops inst sem y1 g k s.1 s.2
  have hloop : Aeneas.Std.loop step (iter,parts)=Result.ok (core.result.Result.Ok out) := hrun
  induction hfuel : 6-iter.start.val generalizing iter parts with
  | zero =>
    have heq : iter.start.val=6 := by omega
    rcases loop_success_cases step (iter,parts) (core.result.Result.Ok out) hloop with hdone | ⟨s,hcont,htail⟩
    · obtain ⟨iter',hnext,hsum⟩ := body_done_ok ops inst sem y1 g k parts iter out hdone
      exact Chain.done iter parts out heq hsum
    · rcases s with ⟨iter',parts'⟩
      obtain ⟨point,i,value,hnext,hdot,hinc,hwrite⟩ := body_cont ops inst sem y1 g k parts parts' iter iter' hcont
      have hactive := (next_some_step iter iter' point hnext).2.1
      omega
  | succ fuel ih =>
    rcases loop_success_cases step (iter,parts) (core.result.Result.Ok out) hloop with hdone | ⟨s,hcont,htail⟩
    · obtain ⟨iter',hnext,hsum⟩ := body_done_ok ops inst sem y1 g k parts iter out hdone
      have hge := next_none_bound iter iter' hnext
      have heq : iter.start.val=6 := by omega
      exact Chain.done iter parts out heq hsum
    · rcases s with ⟨iter',parts'⟩
      obtain ⟨point,i,value,hnext,hdot,hinc,hwrite⟩ := body_cont ops inst sem y1 g k parts parts' iter iter' hcont
      obtain ⟨hpoint,hactive,hstart,hend'⟩ := next_some_step iter iter' point hnext
      have hend1 : iter'.end.val=6 := by rw [hend']; exact hend
      have hi1 : iter'.start.val≤6 := by omega
      have hfnext : 6-iter'.start.val=fuel := by omega
      have hrunNext : verifier.prepared_claim_loop ops inst iter' sem y1 g k parts'=Result.ok (core.result.Result.Ok out) := htail
      have ht := ih parts' iter' hend1 hi1 hrunNext htail hfnext
      exact Chain.step point i value hnext hdot hinc hwrite ht
#print axioms next_some_step
#print axioms next_none_bound
#print axioms successful_loop_has_chain
end AspisR1CurrentPreparedClaim.ClaimTrace
