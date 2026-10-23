import S1ClaimOwnedNestedModelV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1CurrentPreparedClaim.OwnedNestedTransfer
abbrev E := aspis_core.field.WideExact
abbrev Range := core.ops.range.Range Usize

theorem scalar_eq {D H : Type} {N : Usize} (ops : ClaimDotOps D) (sem : r1_semantic.Verified H)
    (y1 : Array U8 N) (point l : Usize) :
    verifier.owned_scalar ops sem.claims sem.extra sem.before_z1 y1 point l =
      ClaimScalar.read ops sem (Array.to_slice y1) point l := by
  have hz : 0#usize ≤ point := by scalar_tac
  simp only [verifier.owned_scalar, ClaimScalar.read, hz, if_true, lift]
  split <;> simp only [bind_tc_ok]
  · rfl

theorem sum_eq (k parts : Array E 7#usize) :
    verifier.owned_sum k parts=verifier.prepared_claim_sum k parts := by rfl

/-- The full semantic owner is framed on both Rust success and Rust error.
This is not an assertion of successful/total execution or native equivalence. -/
theorem owner_frame {D H : Type} (ops : ClaimDotOps D) (inst : aspis_core.Digest32 H)
    (sem returned : r1_semantic.Verified H) (y1 : Array U8 928#usize)
    (inactive kappa : E) (g : Array E 29#usize) (r : core.result.Result E verifier.Error)
    (h : verifier.prepared_claim_owned ops inst sem y1 inactive g kappa = .ok (r,returned)) :
    returned=sem ∧ verifier.owned_claim_loops ops sem.claims sem.extra sem.before_z1 y1 inactive g kappa=.ok r := by
  unfold verifier.prepared_claim_owned at h
  cases hc : verifier.owned_claim_loops ops sem.claims sem.extra sem.before_z1 y1 inactive g kappa with
  | fail e => simp only [hc,bind_tc_fail] at h;cases h
  | div => simp only [hc,bind_tc_div] at h;cases h
  | ok value =>
    simp only [hc,bind_tc_ok] at h
    cases h
    exact ⟨rfl,rfl⟩

def finishPending {D : Type} (ops : ClaimDotOps D)
    (r : D × Option (core.result.Result E verifier.Error)) :
    Result (core.result.Result E verifier.Error) := do
  match r.2 with
  | none => let value ← ops.finishDot r.1; ok (.Ok value)
  | some result => ok result

def ownedStep {D H : Type} {N : Usize} (ops : ClaimDotOps D) (sem : r1_semantic.Verified H)
    (y1 : Array U8 N) (g : Array E 29#usize) (point : Usize) (s : Range × D) :=
  verifier.owned_claim_loops_loop0_loop0.body ops sem.claims sem.extra sem.before_z1 y1 g point s.1 s.2

/-- Finite source-control simulation, including both Rust error and child
failure/divergence. It uses the same arbitrary operations, not accepted-only
or independent child success premises. -/
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
    dsimp only [ownedStep,ClaimDotBoundedResult.step]
    rw [ClaimScalar.body_eq_source]
    simp only [verifier.owned_claim_loops_loop0_loop0.body,ClaimScalar.body,
      verifier.owned_push,scalar_eq,bind_assoc_eq]
    apply bind_congr
    rintro ⟨opt,iter1⟩
    cases opt with
    | none =>
      simp only [bind_tc_ok,finishPending,bind_assoc_eq]
      apply bind_congr
      intro value
      rfl
    | some l =>
      simp only [bind_assoc_eq]
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

#print axioms scalar_eq
#print axioms sum_eq
#print axioms owner_frame
#print axioms bounded_inner_eq
end AspisR1CurrentPreparedClaim.OwnedNestedTransfer
