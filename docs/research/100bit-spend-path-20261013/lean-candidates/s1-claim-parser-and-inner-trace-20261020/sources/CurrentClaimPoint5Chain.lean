import CurrentClaimInnerPoint5Done
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1CurrentPreparedClaim.ClaimInner
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

inductive Point5Chain {D : Type} (ops : ClaimDotOps D) (y1 : Slice U8)
    (g : Array E 29#usize) : Range → D → E → Prop
  | done (iter : Range) (dot : D) (out : E)
      (atEnd : iter.start.val=29) (finish : ops.finishDot dot=Result.ok out) :
      Point5Chain ops y1 g iter dot out
  | step {iter iter' : Range} {dot dot' : D} {out : E}
      (l : Usize) (coeff parsed : E)
      (next : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter=Result.ok (some l,iter'))
      (read : ClaimParser.field y1 l=Result.ok parsed) (canonical : Concrete.Canonical parsed)
      (weight : Array.index_usize g l=Result.ok coeff)
      (push : ops.pushDot dot coeff parsed.c0=Result.ok (core.result.Result.Ok (),dot'))
      (tail : Point5Chain ops y1 g iter' dot' out) : Point5Chain ops y1 g iter dot out

theorem point5_successful_loop_has_chain {D H : Type} (ops : ClaimDotOps D)
    (inst : aspis_core.Digest32 H) (sem : r1_semantic.Verified H)
    (y1 : Slice U8) (g : Array E 29#usize) (iter : Range) (dot : D) (out : E)
    (hend : iter.end.val=29) (hi : iter.start.val≤29)
    (hrun : verifier.prepared_claim_dot_loop (ClaimParser.withParser ops) inst iter sem y1 g
      5#usize dot=Result.ok (core.result.Result.Ok out)) : Point5Chain ops y1 g iter dot out := by
  let step := fun s : Range × r1_semantic.Verified H × Usize × D =>
    verifier.prepared_claim_dot_loop.body (ClaimParser.withParser ops) inst y1 g s.1 s.2.1 s.2.2.1 s.2.2.2
  have hloop : Aeneas.Std.loop step (iter,sem,5#usize,dot)=Result.ok (core.result.Result.Ok out) := hrun
  induction hfuel : 29-iter.start.val generalizing iter dot with
  | zero =>
    have heq : iter.start.val=29 := by omega
    rcases loop_success_cases step (iter,sem,5#usize,dot) (core.result.Result.Ok out) hloop with hdone | ⟨s,hcont,htail⟩
    · obtain ⟨iter',hnext,hfinish⟩ := point5_body_done_ok ops inst sem y1 g iter dot out hdone
      exact Point5Chain.done iter dot out heq hfinish
    · rcases s with ⟨iter',sem',point',dot'⟩
      obtain ⟨hsem,hpoint,l,coeff,parsed,hnext,hfield,hcanon,hweight,hpush⟩ :=
        point5_body_cont ops inst sem sem' y1 g iter iter' point' dot dot' hcont
      have hactive := (ClaimTrace.next_some_step iter iter' l hnext).2.1
      omega
  | succ fuel ih =>
    rcases loop_success_cases step (iter,sem,5#usize,dot) (core.result.Result.Ok out) hloop with hdone | ⟨s,hcont,htail⟩
    · obtain ⟨iter',hnext,hfinish⟩ := point5_body_done_ok ops inst sem y1 g iter dot out hdone
      have hge := ClaimTrace.next_none_bound iter iter' hnext
      have heq : iter.start.val=29 := by omega
      exact Point5Chain.done iter dot out heq hfinish
    · rcases s with ⟨iter',sem',point',dot'⟩
      obtain ⟨hsem,hpoint,l,coeff,parsed,hnext,hfield,hcanon,hweight,hpush⟩ :=
        point5_body_cont ops inst sem sem' y1 g iter iter' point' dot dot' hcont
      subst sem'; subst point'
      obtain ⟨hl,hactive,hstart,hend'⟩ := ClaimTrace.next_some_step iter iter' l hnext
      have hend1 : iter'.end.val=29 := by rw [hend']; exact hend
      have hi1 : iter'.start.val≤29 := by omega
      have hfnext : 29-iter'.start.val=fuel := by omega
      have hrunNext : verifier.prepared_claim_dot_loop (ClaimParser.withParser ops) inst iter' sem y1 g
        5#usize dot'=Result.ok (core.result.Result.Ok out) := htail
      have ht := ih iter' dot' hend1 hi1 hrunNext htail hfnext
      exact Point5Chain.step l coeff parsed hnext hfield hcanon hweight hpush ht

#print axioms point5_successful_loop_has_chain
end AspisR1CurrentPreparedClaim.ClaimInner
