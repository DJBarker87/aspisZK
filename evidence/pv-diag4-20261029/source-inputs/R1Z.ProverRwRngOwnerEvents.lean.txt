import R1Z.ProverRwRngOwnerBridge
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwRngOwnerEvents
open Aeneas Aeneas.Std Result ControlFlow ProverRwRng
open ProverRwRngOwnerStep ProverRwRngOwnerInduction ProverRwRngOwnerBridge
variable [ErasureFns]
abbrev State := Tape × Usize
abbrev newBody (nonce : Array U8 32#usize) : State → Result (ControlFlow State (Tape × Status)) :=
  fun s => StateOnlyAttemptSecrets.generate_with_loop.body
    Tape.Insts.Prover_rw_rng_preflightDraw64 nonce 16#usize s.1 s.2
abbrev oldBody (nonce : Array U8 32#usize) : State → Result (ControlFlow State (Status × Tape)) :=
  fun s => StateOnlyAttemptSecrets.old_loop.body nonce 16#usize s.1 s.2

/-- Every entry is an actual source-body invocation, with its full provider and
retry state. No output-equality premise is part of this execution relation. -/
inductive Replay {R : Type} (body : State → Result (ControlFlow State R)) :
    State → List State → R → Prop
  | finish {s result} (step : body s = .ok (.done result)) : Replay body s [s] result
  | next {s after states result} (step : body s = .ok (.cont after))
      (rest : Replay body after states result) : Replay body s (s :: states) result

theorem replay_old_of_new (nonce : Array U8 32#usize) {s : State} {states : List State}
    {result : Tape × Status} (run : Replay (newBody nonce) s states result) :
    Replay (oldBody nonce) s states (Prod.swap result) := by
  induction run with
  | @finish s result step =>
    rcases result with ⟨after,status⟩
    apply Replay.finish
    have link := body_same nonce 16#usize s.2 s.1
    change oldBody nonce s = mapResult swapDone (newBody nonce s) at link
    rw [link,step]
    rfl
  | @next s after states result step rest ih =>
    apply Replay.next (after := after) _ ih
    have link := body_same nonce 16#usize s.2 s.1
    change oldBody nonce s = mapResult swapDone (newBody nonce s) at link
    rw [link,step]
    rfl

theorem loop_has_replay (nonce : Array U8 32#usize) (p : Tape) (retry : Usize)
    (result : Tape × Status)
    (run : StateOnlyAttemptSecrets.generate_with_loop
      Tape.Insts.Prover_rw_rng_preflightDraw64 nonce p 16#usize retry = .ok result) :
    ∃ states, Replay (newBody nonce) (p,retry) states result := by
  suffices ∀ fuel p retry, 17 - retry.val = fuel →
      StateOnlyAttemptSecrets.generate_with_loop
        Tape.Insts.Prover_rw_rng_preflightDraw64 nonce p 16#usize retry = .ok result →
      ∃ states, Replay (newBody nonce) (p,retry) states result by
    exact this _ p retry rfl run
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | h fuel ih =>
    intro p retry hf run
    change loop (newBody nonce) (p,retry) = .ok result at run
    rw [loop] at run
    cases step : newBody nonce (p,retry) with
    | fail e => rw [step] at run; cases run
    | div => rw [step] at run; cases run
    | ok flow =>
      rw [step] at run
      cases flow with
      | done final =>
        cases run
        exact ⟨[(p,retry)],Replay.finish step⟩
      | cont next =>
        obtain ⟨below,increased⟩ := body_progress nonce p retry next step
        have belowNat : retry.val < 16 := by exact below
        have less : 17 - next.2.val < fuel := by omega
        have recurse : StateOnlyAttemptSecrets.generate_with_loop
            Tape.Insts.Prover_rw_rng_preflightDraw64 nonce next.1 16#usize next.2 = .ok result := by
          simpa only [StateOnlyAttemptSecrets.generate_with_loop,Prod.mk.eta] using run
        obtain ⟨states,rest⟩ := ih _ less next.1 next.2 rfl recurse
        exact ⟨(p,retry)::states,Replay.next step rest⟩

/-- The nonce guard is the actual common emitted scan. A false nonce consumes
no body invocation. The result map only accounts for Rust's borrowed return
order; neither branch assumes an old/new output equality. -/
def OwnerReplay {R : Type} (body : State → Result (ControlFlow State R))
    (resultMap : R → Tape × Status) (nonce : Array U8 32#usize) (p : Tape)
    (states : List State) (result : Tape × Status) : Prop :=
  (entropy_nonzero32 nonce = .ok false ∧ states = [] ∧
    result = (p,.Err .RepeatedZeroBlock)) ∨
  (entropy_nonzero32 nonce = .ok true ∧
    ∃ raw, Replay body (p,0#usize) states raw ∧ resultMap raw = result)

/-- Complete same-control replay, not merely an output observation. Every
intermediate provider/retry state is shared, also on rejects and OS errors. -/
theorem cap16_same_event (nonce : Array U8 32#usize) (p : Tape) :
    old_owner nonce p = owner nonce p ∧
    ∀ after status, owner nonce p = .ok (after,status) →
      ∃ states,
        OwnerReplay (oldBody nonce) Prod.swap nonce p states (after,status) ∧
        OwnerReplay (newBody nonce) id nonce p states (after,status) := by
  refine ⟨owners_same nonce p,?_⟩
  intro after status run
  unfold owner StateOnlyAttemptSecrets.generate_with at run
  cases scan : entropy_nonzero32 nonce with
  | fail e => rw [scan] at run; cases run
  | div => rw [scan] at run; cases run
  | ok b =>
    rw [scan] at run
    cases b with
    | false =>
      simp only [bind_tc_ok,Bool.false_eq_true,if_false,Result.ok.injEq,Prod.mk.injEq] at run
      rcases run with ⟨ha,hs⟩
      subst after
      subst status
      exact ⟨[],Or.inl ⟨scan,rfl,rfl⟩,Or.inl ⟨scan,rfl,rfl⟩⟩
    | true =>
      simp only [bind_tc_ok,if_true] at run
      unfold ENTROPY_RETRY_LIMIT at run
      obtain ⟨states,replay⟩ := loop_has_replay nonce p 0#usize (after,status) run
      exact ⟨states,Or.inr ⟨scan,(status,after),replay_old_of_new nonce replay,rfl⟩,
        Or.inr ⟨scan,(after,status),replay,rfl⟩⟩

#print axioms replay_old_of_new
#print axioms loop_has_replay
#print axioms cap16_same_event
end R1Z.ProverRwRngOwnerEvents
