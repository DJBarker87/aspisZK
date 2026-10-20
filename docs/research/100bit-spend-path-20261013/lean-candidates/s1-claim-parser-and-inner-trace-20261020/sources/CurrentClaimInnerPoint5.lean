import CurrentClaimParserInstance
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1CurrentPreparedClaim.ClaimInner
open Concrete
abbrev Range := core.ops.range.Range Usize
private theorem bind_success {α β : Type} (m : Result α) (k : α → Result β) (v : β)
    (h : (do let x ← m; k x)=Result.ok v) : ∃ x, m=Result.ok x ∧ k x=Result.ok v := by
  cases m with
  | ok x => exact ⟨x,rfl,h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

theorem point5_body_cont {D H : Type} (ops : ClaimDotOps D) (inst : aspis_core.Digest32 H)
    (sem sem' : r1_semantic.Verified H) (y1 : Slice U8) (g : Array E 29#usize)
    (iter iter' : Range) (point' : Usize) (dot dot' : D)
    (h : verifier.prepared_claim_dot_loop.body (ClaimParser.withParser ops) inst
      y1 g iter sem 5#usize dot = Result.ok (ControlFlow.cont (iter',sem',point',dot'))) :
    sem'=sem ∧ point'=5#usize ∧ ∃ l coeff parsed,
      core.iter.range.IteratorRange.next core.iter.range.StepUsize iter=Result.ok (some l,iter') ∧
      ClaimParser.field y1 l=Result.ok parsed ∧ Concrete.Canonical parsed ∧
      Array.index_usize g l=Result.ok coeff ∧
      ops.pushDot dot coeff parsed.c0=Result.ok (core.result.Result.Ok (),dot') := by
  unfold verifier.prepared_claim_dot_loop.body at h
  obtain ⟨pair,hnext,h⟩ := bind_success _ _ _ h
  rcases pair with ⟨opt,iter1⟩
  cases opt with
  | none =>
    obtain ⟨out,hout,h⟩ := bind_success _ _ _ h
    cases h
  | some l =>
    simp only [show (0#usize ≤ 5#usize) from by decide, show ¬(5#usize ≤ 2#usize) from by decide,
      show (5#usize).val=5 from by rfl,if_true,if_false,ClaimParser.withParser,ClaimParser.c0,bind_assoc_eq,bind_tc_ok] at h
    change (do
      let parsed ← ClaimParser.field y1 l
      let coeff ← Array.index_usize g l
      let (r,dot1) ← ops.pushDot dot coeff parsed.c0
      let r1 ← core.result.Result.map_err
        (verifier.prepared_claim_dot.closure.Insts.CoreOpsFunctionFnOnceTupleTupleError inst) r ()
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r1
      match cf with
      | core.ops.control_flow.ControlFlow.Continue _ =>
        Result.ok (ControlFlow.cont (iter1,sem,5#usize,dot1))
      | core.ops.control_flow.ControlFlow.Break residual => do
        let r2 ← core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          aspis_core.field.WideExact (core.convert.FromSame verifier.Error) residual
        Result.ok (ControlFlow.done r2)) = Result.ok (ControlFlow.cont (iter',sem',point',dot')) at h
    obtain ⟨parsed,hfield,h⟩ := bind_success _ _ _ h
    obtain ⟨coeff,hcoeff,h⟩ := bind_success _ _ _ h
    obtain ⟨pair,hpush,h⟩ := bind_success _ _ _ h
    rcases pair with ⟨r,dot1⟩
    cases r with
    | Err e =>
      simp [core.result.Result.map_err,
        verifier.prepared_claim_dot.closure.Insts.CoreOpsFunctionFnOnceTupleTupleError,
        verifier.prepared_claim_dot.closure.Insts.CoreOpsFunctionFnOnceTupleTupleError.call_once,
        core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at h
    | Ok u =>
      cases u
      change Result.ok (ControlFlow.cont (β := core.result.Result E verifier.Error)
        (iter1,sem,5#usize,dot1))=Result.ok (ControlFlow.cont (iter',sem',point',dot')) at h
      have he := ControlFlow.cont.inj (Result.ok.inj h)
      cases he
      exact ⟨rfl,rfl,l,coeff,parsed,hnext,hfield,(ClaimParser.field_success y1 l parsed hfield).1,hcoeff,hpush⟩

#print axioms point5_body_cont
end AspisR1CurrentPreparedClaim.ClaimInner
