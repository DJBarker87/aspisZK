import CurrentClaimScalarNormalForm
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1CurrentPreparedClaim.ClaimScalar
open Concrete
private theorem bind_success {α β : Type} (m : Result α) (k : α → Result β) (v : β)
    (h : (do let x ← m; k x)=Result.ok v) : ∃ x, m=Result.ok x ∧ k x=Result.ok v := by
  cases m with
  | ok x => exact ⟨x,rfl,h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

theorem body_cont {D H : Type} (ops : ClaimDotOps D) (inst : aspis_core.Digest32 H)
    (sem sem' : r1_semantic.Verified H) (y1 : Slice U8) (g : Array E 29#usize)
    (iter iter' : Range) (point point' : Usize) (dot dot' : D)
    (h : verifier.prepared_claim_dot_loop.body ops inst y1 g iter sem point dot=
      Result.ok (ControlFlow.cont (iter',sem',point',dot'))) :
    sem'=sem ∧ point'=point ∧ ∃ l scalar coeff,
      core.iter.range.IteratorRange.next core.iter.range.StepUsize iter=Result.ok (some l,iter') ∧
      read ops sem y1 point l=Result.ok scalar ∧ Array.index_usize g l=Result.ok coeff ∧
      ops.pushDot dot coeff scalar=Result.ok (core.result.Result.Ok (),dot') := by
  rw [body_eq_source] at h
  unfold body at h
  obtain ⟨pair,hnext,h⟩ := bind_success _ _ _ h
  rcases pair with ⟨opt,iter1⟩
  cases opt with
  | none =>
    obtain ⟨out,hout,h⟩ := bind_success _ _ _ h
    cases h
  | some l =>
    obtain ⟨scalar,hread,h⟩ := bind_success _ _ _ h
    obtain ⟨coeff,hcoeff,h⟩ := bind_success _ _ _ h
    obtain ⟨pair,hpush,h⟩ := bind_success _ _ _ h
    rcases pair with ⟨r,dot1⟩
    cases r with
    | Err e =>
      simp [core.result.Result.map_err,
        verifier.prepared_claim_dot.closure.Insts.CoreOpsFunctionFnOnceTupleTupleError.call_once,
        core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at h
    | Ok u =>
      cases u
      change Result.ok (ControlFlow.cont (β := core.result.Result E verifier.Error)
        (iter1,sem,point,dot1))=Result.ok (ControlFlow.cont (iter',sem',point',dot')) at h
      have he := ControlFlow.cont.inj (Result.ok.inj h)
      cases he
      exact ⟨rfl,rfl,l,scalar,coeff,hnext,hread,hcoeff,hpush⟩

theorem body_done_ok {D H : Type} (ops : ClaimDotOps D) (inst : aspis_core.Digest32 H)
    (sem : r1_semantic.Verified H) (y1 : Slice U8) (g : Array E 29#usize)
    (iter : Range) (point : Usize) (dot : D) (out : E)
    (h : verifier.prepared_claim_dot_loop.body ops inst y1 g iter sem point dot=
      Result.ok (ControlFlow.done (core.result.Result.Ok out))) :
    ∃ iter', core.iter.range.IteratorRange.next core.iter.range.StepUsize iter=Result.ok (none,iter') ∧
      ops.finishDot dot=Result.ok out := by
  rw [body_eq_source] at h
  unfold body at h
  obtain ⟨pair,hnext,h⟩ := bind_success _ _ _ h
  rcases pair with ⟨opt,iter1⟩
  cases opt with
  | none =>
    obtain ⟨value,hfinish,h⟩ := bind_success _ _ _ h
    have he : value=out := core.result.Result.Ok.inj (ControlFlow.done.inj (Result.ok.inj h))
    subst value
    exact ⟨iter1,hnext,hfinish⟩
  | some l =>
    obtain ⟨scalar,hread,h⟩ := bind_success _ _ _ h
    obtain ⟨coeff,hcoeff,h⟩ := bind_success _ _ _ h
    obtain ⟨pair,hpush,h⟩ := bind_success _ _ _ h
    rcases pair with ⟨r,dot1⟩
    cases r with
    | Err e =>
      simp [core.result.Result.map_err,
        verifier.prepared_claim_dot.closure.Insts.CoreOpsFunctionFnOnceTupleTupleError.call_once,
        core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at h
    | Ok u =>
      cases u
      change Result.ok (ControlFlow.cont (β := core.result.Result E verifier.Error)
        (iter1,sem,point,dot1))=Result.ok (ControlFlow.done (core.result.Result.Ok out)) at h
      cases h

#print axioms body_cont
#print axioms body_done_ok
end AspisR1CurrentPreparedClaim.ClaimScalar
