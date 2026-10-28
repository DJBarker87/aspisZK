import R1Z.ProverRwRngCallerEmission
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwRngCallerControl
open Aeneas Aeneas.Std Result ProverRwRngCaller
variable [NativeTypes] [ErasureFns]
abbrev Policy (N : Type) := core.ops.function.FnMut N Usize (Array U8 32#usize)
abbrev Body (B L : Type) := core.ops.function.FnMut B (StateOnlyAttemptSecrets × L)
  (L × core.result.Result (alloc.vec.Vec U8 × U64) ProverRwRngCaller.Error)
def mapped (r : core.result.Result StateOnlyAttemptSecrets StateOnlyAttemptEntropyError) :
    core.result.Result StateOnlyAttemptSecrets ProverRwRngCaller.Error :=
  match r with | .Ok a => .Ok a | .Err _ => .Err .Entropy

theorem native_from (e : getrandom.error.Error) :
    StateOnlyAttemptEntropyError.Insts.CoreConvertFromError.from e =
      .ok (.Os e) := rfl

theorem callback_step {N : Type} (policy : Policy N) (p p' : Tape) (n n' : N)
    (k : Usize) (nonce : Array U8 32#usize)
    (r : core.result.Result StateOnlyAttemptSecrets StateOnlyAttemptEntropyError)
    (hpolicy : policy.call_mut n k = .ok (nonce,n'))
    (hentropy : StateOnlyAttemptSecrets.generate_with
      Tape.Insts.Prover_rw_rng_callerDraw64 nonce p = .ok (p',r)) :
    selected_callback policy p n k = .ok (p',n',mapped r) := by
  unfold selected_callback
  rw [hpolicy]
  simp only [bind_tc_ok,Aeneas.Std.uncurry]
  rw [hentropy]
  cases r <;> rfl

theorem variant_guard {N L B : Type} (policy : Policy N) (body : Body B L)
    (p : Tape) (n : N) (l : L) (b : B) :
    prove_masked_retrying_with policy body false p n l b =
      .ok (p,n,l,b,.Err .Semantic) := rfl

theorem cap_guard {N L B : Type} (policy : Policy N) (body : Body B L)
    (p : Tape) (n : N) (l : L) (b : B) (k : Usize) (cap : k ≥ 8#usize) :
    retry_attempt policy body p n l b k = .ok (p,n,l,b,.Err .AttemptsExhausted) := by
  rw [retry_attempt]
  simpa only [ATTEMPT_CAP,if_pos cap]

theorem callback_error {N L B : Type} (policy : Policy N) (body : Body B L)
    (p p' : Tape) (n n' : N) (l : L) (b : B) (k : Usize)
    (below : ¬ k ≥ 8#usize) (e : ProverRwRngCaller.Error)
    (callback : selected_callback policy p n k = .ok (p',n',.Err e)) :
    retry_attempt policy body p n l b k = .ok (p',n',l,b,.Err e) := by
  rw [retry_attempt]
  simp only [ATTEMPT_CAP,if_neg below,callback,bind_tc_ok,Aeneas.Std.uncurry]

theorem body_fatal {N L B : Type} (policy : Policy N) (body : Body B L)
    (p p' : Tape) (n n' : N) (l l' : L) (b b' : B) (k : Usize)
    (below : ¬ k ≥ 8#usize) (a : StateOnlyAttemptSecrets)
    (e : ProverRwRngCaller.Error) (fatal : e ≠ .Rejected)
    (callback : selected_callback policy p n k = .ok (p',n',.Ok a))
    (hbody : body.call_mut b (a,l) = .ok ((l',.Err e),b')) :
    retry_attempt policy body p n l b k = .ok (p',n',l',b',.Err e) := by
  rw [retry_attempt]
  simp only [ATTEMPT_CAP,if_neg below,callback,bind_tc_ok,Aeneas.Std.uncurry,hbody]
  cases e <;> first | rfl | exact False.elim (fatal rfl)

theorem body_rejected {N L B : Type} (policy : Policy N) (body : Body B L)
    (p p' : Tape) (n n' : N) (l l' : L) (b b' : B) (k next : Usize)
    (below : ¬ k ≥ 8#usize) (a : StateOnlyAttemptSecrets)
    (callback : selected_callback policy p n k = .ok (p',n',.Ok a))
    (hbody : body.call_mut b (a,l) = .ok ((l',.Err .Rejected),b'))
    (increment : (k + 1#usize : Result Usize) = .ok next) :
    retry_attempt policy body p n l b k = retry_attempt policy body p' n' l' b' next := by
  rw [retry_attempt]
  simp only [ATTEMPT_CAP,if_neg below,callback,bind_tc_ok,Aeneas.Std.uncurry,hbody,increment]

theorem body_success {N L B : Type} (policy : Policy N) (body : Body B L)
    (p p' : Tape) (n n' : N) (l l' : L) (b b' : B) (k next : Usize)
    (below : ¬ k ≥ 8#usize) (a : StateOnlyAttemptSecrets)
    (proof : alloc.vec.Vec U8) (audit : U64)
    (callback : selected_callback policy p n k = .ok (p',n',.Ok a))
    (hbody : body.call_mut b (a,l) = .ok ((l',.Ok (proof,audit)),b'))
    (increment : (k + 1#usize : Result Usize) = .ok next) :
    retry_attempt policy body p n l b k =
      .ok (p',n',l',b',.Ok {proof,audit,attempts := next}) := by
  rw [retry_attempt]
  simp only [ATTEMPT_CAP,if_neg below,callback,bind_tc_ok,Aeneas.Std.uncurry,hbody,increment]

theorem increment_safe (k : Usize) (below : k < 8#usize) :
    ∃ next : Usize, (k + 1#usize : Result Usize) = .ok next ∧ next.val = k.val + 1 := by
  have safe : k.val + (1#usize).val ≤ Usize.max := by scalar_tac
  obtain ⟨next,he,hv⟩ := WP.spec_imp_exists (Usize.add_spec (x := k) (y := 1#usize) safe)
  exact ⟨next,he,by simpa only [show (1#usize).val = 1 by scalar_tac] using hv⟩

#print axioms native_from
#print axioms callback_step
#print axioms variant_guard
#print axioms cap_guard
#print axioms callback_error
#print axioms body_fatal
#print axioms body_rejected
#print axioms body_success
#print axioms increment_safe
end R1Z.ProverRwRngCallerControl
