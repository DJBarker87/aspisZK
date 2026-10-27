import R1Z.ProverRwRngCallerControl
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwRngCallerStep
open Aeneas Aeneas.Std Result ControlFlow ProverRwRngCaller
open ProverRwRngCallerControl
variable [NativeTypes] [ErasureFns]
def retry_step
  {N : Type} {L : Type} {B : Type}
  (coreopsfunctionFnMutNTupleUsizeArrayU832Inst : core.ops.function.FnMut N
  Std.Usize (Array Std.U8 32#usize))
  (coreopsfunctionFnMutBPairStateOnlyAttemptSecretsLPairLResultPairVecU8U64ErrorInst
  : core.ops.function.FnMut B (StateOnlyAttemptSecrets × L) (L ×
  (core.result.Result ((alloc.vec.Vec Std.U8) × Std.U64) ProverRwRngCaller.Error)))
  (tape : Tape) (proof_account : N) (nonce_store : L) (body : B)
  (k : Std.Usize) :
  Result (ControlFlow (Tape × N × L × B × Std.Usize)
    (Tape × N × L × B × (core.result.Result RetriedProof ProverRwRngCaller.Error)))
  := do
  if k >= ATTEMPT_CAP
  then
    ok (done (tape, proof_account, nonce_store, body, core.result.Result.Err
      Error.AttemptsExhausted))
  else
    let (tape1, proof_account1, status) ←
      selected_callback coreopsfunctionFnMutNTupleUsizeArrayU832Inst tape
        proof_account k
    match status with
    | core.result.Result.Ok a =>
      let ((after_store, result), body1) ←
        coreopsfunctionFnMutBPairStateOnlyAttemptSecretsLPairLResultPairVecU8U64ErrorInst.call_mut
          body (a, nonce_store)
      match result with
      | core.result.Result.Ok p =>
        let (proof, audit) := p
        let i ← k + 1#usize
        ok (done (tape1, proof_account1, after_store, body1, core.result.Result.Ok
          { proof, audit, attempts := i }))
      | core.result.Result.Err e =>
        match e with
        | Error.Parse =>
          ok (done (tape1, proof_account1, after_store, body1, core.result.Result.Err
            Error.Parse))
        | Error.Semantic =>
          ok (done (tape1, proof_account1, after_store, body1, core.result.Result.Err
            Error.Semantic))
        | Error.Transcript =>
          ok (done (tape1, proof_account1, after_store, body1, core.result.Result.Err
            Error.Transcript))
        | Error.Relation =>
          ok (done (tape1, proof_account1, after_store, body1, core.result.Result.Err
            Error.Relation))
        | Error.Merkle =>
          ok (done (tape1, proof_account1, after_store, body1, core.result.Result.Err
            Error.Merkle))
        | Error.Query =>
          ok (done (tape1, proof_account1, after_store, body1, core.result.Result.Err
            Error.Query))
        | Error.Checkpoint =>
          ok (done (tape1, proof_account1, after_store, body1, core.result.Result.Err
            Error.Checkpoint))
        | Error.Allocation =>
          ok (done (tape1, proof_account1, after_store, body1, core.result.Result.Err
            Error.Allocation))
        | Error.Rejected =>
          let i ← k + 1#usize
          ok (cont (tape1, proof_account1, after_store, body1, i))
        | Error.AttemptsExhausted =>
          ok (done (tape1, proof_account1, after_store, body1, core.result.Result.Err
            Error.AttemptsExhausted))
        | Error.Entropy =>
          ok (done (tape1, proof_account1, after_store, body1, core.result.Result.Err
            Error.Entropy))
    | core.result.Result.Err e =>
      ok (done (tape1, proof_account1, nonce_store, body, core.result.Result.Err e))

theorem retry_factor {N L B : Type} (policy : Policy N) (body : Body B L)
    (p : Tape) (n : N) (l : L) (b : B) (k : Usize) :
    retry_attempt policy body p n l b k = (do
      let flow ← retry_step policy body p n l b k
      match flow with
      | .done output => .ok output
      | .cont (p',n',l',b',next) => retry_attempt policy body p' n' l' b' next) := by
  conv_lhs => rw [retry_attempt]
  unfold retry_step
  split
  · rfl
  · simp only [bind_assoc_eq]
    apply (bind_eq_iff _ _ _).mpr
    rintro ⟨p',n',status⟩ hcallback
    simp only [Aeneas.Std.uncurry]
    cases status with
    | Err e => rfl
    | Ok a =>
      simp only [bind_assoc_eq]
      apply (bind_eq_iff _ _ _).mpr
      rintro ⟨⟨l',r⟩,b'⟩ hbody
      simp only [Aeneas.Std.uncurry]
      cases r with
      | Ok pair =>
        rcases pair with ⟨proof,audit⟩
        simp only [bind_assoc_eq]
        apply (bind_eq_iff _ _ _).mpr
        intro next hadd
        rfl
      | Err e =>
        cases e <;> try rfl
        simp only [bind_assoc_eq]
        apply (bind_eq_iff _ _ _).mpr
        intro next hadd
        rfl

def Continues {A C : Type} (p : A → Prop) (r : Result (ControlFlow A C)) : Prop :=
  ∀ next, r = .ok (.cont next) → p next

theorem continues_bind {A B C : Type} (p : B → Prop) (x : Result A)
    (f : A → Result (ControlFlow B C)) (h : ∀ a, Continues p (f a)) :
    Continues p (x >>= f) := by
  cases x with
  | ok a => exact h a
  | fail e => intro next impossible; cases impossible
  | div => intro next impossible; cases impossible

theorem step_progress {N L B : Type} (policy : Policy N) (body : Body B L)
    (p : Tape) (n : N) (l : L) (b : B) (k : Usize) :
    Continues (fun next : Tape × N × L × B × Usize =>
      k.val < 8 ∧ next.2.2.2.2.val = k.val + 1)
      (retry_step policy body p n l b k) := by
  unfold retry_step
  split
  · intro next h; cases h
  · rename_i below
    unfold ATTEMPT_CAP at below
    have low : k < 8#usize := by scalar_tac
    obtain ⟨next,add,hval⟩ := increment_safe k low
    apply continues_bind
    rintro ⟨p',n',status⟩
    simp only [Aeneas.Std.uncurry]
    cases status with
    | Err e => intro next h; cases h
    | Ok a =>
      apply continues_bind
      rintro ⟨⟨l',r⟩,b'⟩
      simp only [Aeneas.Std.uncurry]
      cases r with
      | Ok pair =>
        rcases pair with ⟨proof,audit⟩
        simp only [add,bind_tc_ok]
        intro next h; cases h
      | Err e =>
        cases e <;> try (intro next h; cases h)
        simp only [add,bind_tc_ok]
        intro state h
        cases h
        exact ⟨low,hval⟩

#print axioms retry_factor
#print axioms continues_bind
#print axioms step_progress
end R1Z.ProverRwRngCallerStep
