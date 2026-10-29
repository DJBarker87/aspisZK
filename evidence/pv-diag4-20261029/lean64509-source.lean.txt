import R1Z.ProverRwRngOwnerInduction
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwRngOwnerBridge
open Aeneas Aeneas.Std Result ControlFlow ProverRwRng
open ProverRwRngOwnerStep ProverRwRngOwnerInduction
variable [ErasureFns]

theorem loops_same (nonce : Array U8 32#usize) (p : Tape) (retry : Usize) :
    StateOnlyAttemptSecrets.old_loop nonce p 16#usize retry =
      mapResult Prod.swap (StateOnlyAttemptSecrets.generate_with_loop
        Tape.Insts.Prover_rw_rng_preflightDraw64 nonce p 16#usize retry) := by
  suffices ∀ fuel p retry, 17 - retry.val = fuel →
      StateOnlyAttemptSecrets.old_loop nonce p 16#usize retry =
        mapResult Prod.swap (StateOnlyAttemptSecrets.generate_with_loop
          Tape.Insts.Prover_rw_rng_preflightDraw64 nonce p 16#usize retry) by
    exact this _ p retry rfl
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | h fuel ih =>
    intro p retry hf
    let oldStep : Tape × Usize → Result (ControlFlow (Tape × Usize) (Status × Tape)) :=
      fun state => StateOnlyAttemptSecrets.old_loop.body nonce 16#usize state.1 state.2
    let newStep : Tape × Usize → Result (ControlFlow (Tape × Usize) (Tape × Status)) :=
      fun state => StateOnlyAttemptSecrets.generate_with_loop.body
        Tape.Insts.Prover_rw_rng_preflightDraw64 nonce 16#usize state.1 state.2
    change loop oldStep (p,retry) = mapResult Prod.swap (loop newStep (p,retry))
    conv_lhs => rw [loop]
    conv_rhs => rw [loop]
    simp only [oldStep,newStep]
    rw [body_same]
    cases step : StateOnlyAttemptSecrets.generate_with_loop.body
      Tape.Insts.Prover_rw_rng_preflightDraw64 nonce 16#usize p retry with
    | fail e => rfl
    | div => rfl
    | ok flow =>
      cases flow with
      | done result => rcases result with ⟨after,status⟩; rfl
      | cont next =>
        obtain ⟨below,increased⟩ := body_progress nonce p retry next step
        have belowNat : retry.val < 16 := by exact below
        have less : 17 - next.2.val < fuel := by omega
        have recurse := ih _ less next.1 next.2 rfl
        simpa only [StateOnlyAttemptSecrets.old_loop,StateOnlyAttemptSecrets.generate_with_loop,
          mapResult,bind_tc_ok,swapDone,Prod.mk.eta] using recurse

/-- All nonces and all finite providers, including every u8 OS-error tag and
arbitrary partial writes. Equality includes the entire returned provider.
Extraction-level tape unavailability is preserved as extraction failure. -/
theorem owners_same (nonce : Array U8 32#usize) (p : Tape) :
    old_owner nonce p = owner nonce p := by
  unfold old_owner StateOnlyAttemptSecrets.old owner StateOnlyAttemptSecrets.generate_with
  cases admitted : entropy_nonzero32 nonce with
  | fail e => rfl
  | div => rfl
  | ok b =>
    cases b with
    | false => rfl
    | true =>
      simp only [bind_tc_ok,if_true]
      unfold ENTROPY_RETRY_LIMIT
      rw [loops_same]
      cases StateOnlyAttemptSecrets.generate_with_loop
        Tape.Insts.Prover_rw_rng_preflightDraw64 nonce p 16#usize 0#usize with
      | fail e => rfl
      | div => rfl
      | ok result => rcases result with ⟨after,status⟩; rfl

#print axioms loops_same
#print axioms owners_same
end R1Z.ProverRwRngOwnerBridge
