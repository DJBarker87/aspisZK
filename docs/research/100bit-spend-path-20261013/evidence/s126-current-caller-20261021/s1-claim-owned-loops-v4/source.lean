import S1ClaimOwnedNestedTransferV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1CurrentPreparedClaim.OwnedNestedTransfer

theorem ownedStep_normal {D H : Type} {N : Usize} (ops : ClaimDotOps D)
    (sem : r1_semantic.Verified H) (y1 : Array U8 N) (g : Array E 29#usize)
    (point : Usize) (iter : Range) (dot : D) :
    ownedStep ops sem y1 g point (iter,dot) = (do
      let (o,iter1) ← core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
      match o with
      | none => ok (.done (dot,none))
      | some l => ownedActive ops sem y1 g iter1 point l dot) := by
  unfold ownedStep verifier.owned_claim_loops_loop0_loop0.body
  apply bind_congr
  rintro ⟨opt,iter1⟩
  cases opt with
  | none => rfl
  | some l =>
    simp only [scalar_eq,verifier.owned_push,ownedActive,bind_assoc_eq]
    rfl

/-- Same finite execution on both extracted loop shapes, with every primitive
failure/divergence and Rust error retained. No accepted-only premise. -/
theorem bounded_inner_eq {D H : Type} {N : Usize} (ops : ClaimDotOps D) (inst : aspis_core.Digest32 H)
    (sem : r1_semantic.Verified H) (y1 : Array U8 N)
    (g : Array E 29#usize) (point : Usize) (n : Nat) (iter : Range) (dot : D) :
    (do let r ← ClaimDotBoundedResult.bounded (ownedStep ops sem y1 g point) n (iter,dot)
        finishPending ops r) =
      ClaimDotBoundedResult.bounded (ClaimDotBoundedResult.step ops inst (Array.to_slice y1) g)
        n (iter,sem,point,dot) := by
  induction n generalizing iter dot with
  | zero => rfl
  | succ n ih =>
    rw [ClaimDotBoundedResult.bounded,ClaimDotBoundedResult.bounded]
    dsimp only [ClaimDotBoundedResult.step]
    rw [ClaimScalar.body_eq_source]
    cases hn : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter with
    | fail e =>
      simp only [ownedStep,verifier.owned_claim_loops_loop0_loop0.body,ClaimScalar.body,hn,bind_tc_fail]
    | div =>
      simp only [ownedStep,verifier.owned_claim_loops_loop0_loop0.body,ClaimScalar.body,hn,bind_tc_div]
    | ok pair =>
      rcases pair with ⟨opt,iter1⟩
      cases opt with
      | none =>
        have hs : ownedStep ops sem y1 g point (iter,dot) = .ok (.done (dot,none)) := by
          unfold ownedStep verifier.owned_claim_loops_loop0_loop0.body
          rw [hn]
          rfl
        rw [hs]
        simp only [ClaimScalar.body,hn,bind_tc_ok,finishPending,bind_assoc_eq]
      | some l =>
        rw [owned_step_some ops sem y1 g point l iter iter1 dot hn]
        simp only [ClaimScalar.body,hn,ownedActive,bind_tc_ok,bind_assoc_eq]
        apply bind_congr
        intro scalar
        apply bind_congr
        intro coeff
        apply bind_congr
        rintro ⟨r,dot1⟩
        cases r with
        | Err u =>
          cases u
          simp [ownedIsErr,finishPending,core.result.Result.map_err,
            verifier.prepared_claim_dot.closure.Insts.CoreOpsFunctionFnOnceTupleTupleError.call_once,
            core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
        | Ok u =>
          cases u
          simp only [bind_tc_ok,ownedIsErr,if_false,core.result.Result.map_err,
            core.result.Result.Insts.CoreOpsTry.branch]
          exact ih iter1 dot1

#print axioms ownedStep_normal
#print axioms bounded_inner_eq
end AspisR1CurrentPreparedClaim.OwnedNestedTransfer
