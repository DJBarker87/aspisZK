import S1ClaimOwnedInnerCompleteV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1CurrentPreparedClaim.OwnedNestedTransfer

def interpretPending {D A : Type} (ops : ClaimDotOps D)
    (kont : core.result.Result E verifier.Error → Result A) (early : E → Result A)
    (r : D × Option (core.result.Result E verifier.Error)) : Result A := do
  match r.2 with
  | none => let value ← ops.finishDot r.1;kont (.Ok value)
  | some (.Err error) => kont (.Err error)
  | some (.Ok value) => early value

/-- Contextual simulation also excludes the impossible early-Ok pending
return. No success, totality or desired-output premise is needed. -/
theorem bounded_inner_cps {D H A : Type} {N : Usize} (ops : ClaimDotOps D)
    (inst : aspis_core.Digest32 H) (sem : r1_semantic.Verified H)
    (y1 : Array U8 N) (g : Array E 29#usize) (point : Usize)
    (kont : core.result.Result E verifier.Error → Result A) (early : E → Result A)
    (n : Nat) (iter : Range) (dot : D) :
    (do let r ← ClaimDotBoundedResult.bounded (ownedStep ops sem y1 g point) n (iter,dot)
        interpretPending ops kont early r) =
    (do let r ← ClaimDotBoundedResult.bounded
          (ClaimDotBoundedResult.step ops inst (Array.to_slice y1) g) n (iter,sem,point,dot)
        kont r) := by
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
        simp only [ClaimScalar.body,hn,bind_tc_ok,interpretPending,bind_assoc_eq]
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
          simp [ownedIsErr,interpretPending,core.result.Result.map_err,
            verifier.prepared_claim_dot.closure.Insts.CoreOpsFunctionFnOnceTupleTupleError.call_once,
            core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
        | Ok u =>
          cases u
          simp only [bind_tc_ok,ownedIsErr,core.result.Result.map_err,
            core.result.Result.Insts.CoreOpsTry.branch]
          exact ih iter1 dot1

theorem complete_inner_cps {D H A : Type} {N : Usize} (ops : ClaimDotOps D)
    (inst : aspis_core.Digest32 H) (sem : r1_semantic.Verified H)
    (y1 : Array U8 N) (g : Array E 29#usize) (point : Usize)
    (kont : core.result.Result E verifier.Error → Result A) (early : E → Result A)
    (iter : Range) (dot : D) (hend : iter.end.val=29) (hstart : iter.start.val≤29) :
    (do let r ← verifier.owned_claim_loops_loop0_loop0 ops iter sem.claims sem.extra sem.before_z1 y1 g point dot
        interpretPending ops kont early r) =
    (do let r ← verifier.prepared_claim_dot_loop ops inst iter sem (Array.to_slice y1) g point dot
        kont r) := by
  rw [owned_loop_eq_bounded ops sem y1 g point iter dot hend hstart,
    ClaimDotBoundedResult.source_loop_eq_bounded ops inst iter sem (Array.to_slice y1) g point dot hend hstart]
  exact bounded_inner_cps ops inst sem y1 g point kont early _ iter dot

#print axioms bounded_inner_cps
#print axioms complete_inner_cps
end AspisR1CurrentPreparedClaim.OwnedNestedTransfer
