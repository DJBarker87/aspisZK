import CurrentClaimPowersInstance
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1CurrentPreparedClaim.ClaimTrace
open Concrete
abbrev Range := core.ops.range.Range Usize
private theorem bind_success {α β : Type} (m : Result α) (k : α → Result β) (v : β)
    (h : (do let x ← m; k x)=Result.ok v) : ∃ x, m=Result.ok x ∧ k x=Result.ok v := by
  cases m with
  | ok x => exact ⟨x,rfl,h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

theorem body_cont {D H : Type} (ops : ClaimDotOps D) (inst : aspis_core.Digest32 H)
    (sem : r1_semantic.Verified H) (y1 : Slice U8) (g : Array E 29#usize)
    (k parts parts' : Array E 7#usize) (iter iter' : Range)
    (h : verifier.prepared_claim_loop.body ops inst sem y1 g k iter parts=Result.ok (ControlFlow.cont (iter',parts'))) :
    ∃ point i value,
      core.iter.range.IteratorRange.next core.iter.range.StepUsize iter=Result.ok (some point,iter') ∧
      verifier.prepared_claim_dot ops inst sem y1 g point=Result.ok (core.result.Result.Ok value) ∧
      (point+1#usize : Result Usize)=Result.ok i ∧ Array.update parts i value=Result.ok parts' := by
  unfold verifier.prepared_claim_loop.body at h
  obtain ⟨pair,hnext,h⟩ := bind_success _ _ _ h
  rcases pair with ⟨opt,iter1⟩
  cases opt with
  | none =>
    change (do let x ← verifier.prepared_claim_sum k parts
               Result.ok (ControlFlow.done (α := Range × Array E 7#usize) ((core.result.Result.Ok x) : core.result.Result E verifier.Error))) =
      Result.ok (ControlFlow.cont (iter',parts')) at h
    obtain ⟨x,hx,h⟩ := bind_success _ _ _ h
    cases h
  | some point =>
    obtain ⟨r,hdot,h⟩ := bind_success _ _ _ h
    cases r with
    | Err err =>
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at h
    | Ok value =>
      change (do let i ← (point+1#usize : Result Usize)
                 let a ← Array.update parts i value
                 Result.ok (ControlFlow.cont (β := core.result.Result E verifier.Error) (iter1,a))) =
        Result.ok (ControlFlow.cont (iter',parts')) at h
      obtain ⟨i,hinc,h⟩ := bind_success _ _ _ h
      obtain ⟨a,hupdate,h⟩ := bind_success _ _ _ h
      have he : (iter1,a)=(iter',parts') := ControlFlow.cont.inj (Result.ok.inj h)
      rcases Prod.mk.inj he with ⟨rfl,rfl⟩
      exact ⟨point,i,value,hnext,hdot,hinc,hupdate⟩

theorem body_done_ok {D H : Type} (ops : ClaimDotOps D) (inst : aspis_core.Digest32 H)
    (sem : r1_semantic.Verified H) (y1 : Slice U8) (g : Array E 29#usize)
    (k parts : Array E 7#usize) (iter : Range) (out : E)
    (h : verifier.prepared_claim_loop.body ops inst sem y1 g k iter parts=
      Result.ok (ControlFlow.done (core.result.Result.Ok out))) :
    ∃ iter', core.iter.range.IteratorRange.next core.iter.range.StepUsize iter=Result.ok (none,iter') ∧
      verifier.prepared_claim_sum k parts=Result.ok out := by
  unfold verifier.prepared_claim_loop.body at h
  obtain ⟨pair,hnext,h⟩ := bind_success _ _ _ h
  rcases pair with ⟨opt,iter1⟩
  cases opt with
  | none =>
    change (do let x ← verifier.prepared_claim_sum k parts
               Result.ok (ControlFlow.done (α := Range × Array E 7#usize) ((core.result.Result.Ok x) : core.result.Result E verifier.Error))) =
      Result.ok (ControlFlow.done (core.result.Result.Ok out)) at h
    obtain ⟨x,hx,h⟩ := bind_success _ _ _ h
    have he : x=out := core.result.Result.Ok.inj (ControlFlow.done.inj (Result.ok.inj h))
    subst x
    exact ⟨iter1,hnext,hx⟩
  | some point =>
    obtain ⟨r,hdot,h⟩ := bind_success _ _ _ h
    cases r with
    | Err err =>
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at h
    | Ok value =>
      change (do let i ← (point+1#usize : Result Usize)
                 let a ← Array.update parts i value
                 Result.ok (ControlFlow.cont (β := core.result.Result E verifier.Error) (iter1,a))) =
        Result.ok (ControlFlow.done (core.result.Result.Ok out)) at h
      obtain ⟨i,hinc,h⟩ := bind_success _ _ _ h
      obtain ⟨a,hupdate,h⟩ := bind_success _ _ _ h
      cases h
#print axioms body_cont
#print axioms body_done_ok
end AspisR1CurrentPreparedClaim.ClaimTrace
