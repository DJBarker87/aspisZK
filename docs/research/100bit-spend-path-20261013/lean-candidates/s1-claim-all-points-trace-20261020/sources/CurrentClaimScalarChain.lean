import CurrentClaimScalarBody
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1CurrentPreparedClaim.ClaimScalar
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

inductive Chain {D H : Type} (ops : ClaimDotOps D) (sem : r1_semantic.Verified H)
    (y1 : Slice U8) (g : Array E 29#usize) (point : Usize) : Range → D → E → Prop
  | done (iter : Range) (dot : D) (out : E)
      (atEnd : iter.start.val=29) (finish : ops.finishDot dot=Result.ok out) :
      Chain ops sem y1 g point iter dot out
  | step {iter iter' : Range} {dot dot' : D} {out : E}
      (l : Usize) (coeff : E) (scalar : aspis_core.field.QM31)
      (next : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter=Result.ok (some l,iter'))
      (read : ClaimScalar.read ops sem y1 point l=Result.ok scalar)
      (weight : Array.index_usize g l=Result.ok coeff)
      (push : ops.pushDot dot coeff scalar=Result.ok (core.result.Result.Ok (),dot'))
      (tail : Chain ops sem y1 g point iter' dot' out) : Chain ops sem y1 g point iter dot out

theorem successful_loop_has_chain {D H : Type} (ops : ClaimDotOps D)
    (inst : aspis_core.Digest32 H) (sem : r1_semantic.Verified H)
    (y1 : Slice U8) (g : Array E 29#usize) (point : Usize) (iter : Range) (dot : D) (out : E)
    (hend : iter.end.val=29) (hi : iter.start.val≤29)
    (hrun : verifier.prepared_claim_dot_loop ops inst iter sem y1 g
      point dot=Result.ok (core.result.Result.Ok out)) : Chain ops sem y1 g point iter dot out := by
  let step := fun s : Range × r1_semantic.Verified H × Usize × D =>
    verifier.prepared_claim_dot_loop.body ops inst y1 g s.1 s.2.1 s.2.2.1 s.2.2.2
  have hloop : Aeneas.Std.loop step (iter,sem,point,dot)=Result.ok (core.result.Result.Ok out) := hrun
  induction hfuel : 29-iter.start.val generalizing iter dot with
  | zero =>
    have heq : iter.start.val=29 := by omega
    rcases loop_success_cases step (iter,sem,point,dot) (core.result.Result.Ok out) hloop with hdone | ⟨s,hcont,htail⟩
    · obtain ⟨iter',hnext,hfinish⟩ := body_done_ok ops inst sem y1 g iter point dot out hdone
      exact Chain.done iter dot out heq hfinish
    · rcases s with ⟨iter',sem',point',dot'⟩
      obtain ⟨hsem,hpoint,l,scalar,coeff,hnext,hread,hweight,hpush⟩ :=
        body_cont ops inst sem sem' y1 g iter iter' point point' dot dot' hcont
      have hactive := (ClaimTrace.next_some_step iter iter' l hnext).2.1
      omega
  | succ fuel ih =>
    rcases loop_success_cases step (iter,sem,point,dot) (core.result.Result.Ok out) hloop with hdone | ⟨s,hcont,htail⟩
    · obtain ⟨iter',hnext,hfinish⟩ := body_done_ok ops inst sem y1 g iter point dot out hdone
      have hge := ClaimTrace.next_none_bound iter iter' hnext
      have heq : iter.start.val=29 := by omega
      exact Chain.done iter dot out heq hfinish
    · rcases s with ⟨iter',sem',point',dot'⟩
      obtain ⟨hsem,hpoint,l,scalar,coeff,hnext,hread,hweight,hpush⟩ :=
        body_cont ops inst sem sem' y1 g iter iter' point point' dot dot' hcont
      subst sem'; subst point'
      obtain ⟨hl,hactive,hstart,hend'⟩ := ClaimTrace.next_some_step iter iter' l hnext
      have hend1 : iter'.end.val=29 := by rw [hend']; exact hend
      have hi1 : iter'.start.val≤29 := by omega
      have hfnext : 29-iter'.start.val=fuel := by omega
      have hrunNext : verifier.prepared_claim_dot_loop ops inst iter' sem y1 g
        point dot'=Result.ok (core.result.Result.Ok out) := htail
      have ht := ih iter' dot' hend1 hi1 hrunNext htail hfnext
      exact Chain.step l coeff scalar hnext hread hweight hpush ht

#print axioms successful_loop_has_chain
end AspisR1CurrentPreparedClaim.ClaimScalar
