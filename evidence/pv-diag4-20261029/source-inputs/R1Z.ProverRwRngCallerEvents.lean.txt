import R1Z.ProverRwRngCallerComposition
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwRngCallerEvents
open Aeneas Aeneas.Std Result ControlFlow ProverRwRngCaller
open ProverRwRngCallerControl ProverRwRngCallerReplay ProverRwRngCallerStep
variable [NativeTypes] [ErasureFns]

theorem callback_invocation {N : Type} (policy : Policy N) (p : Tape) (n : N)
    (k : Usize) (out : Tape × N × core.result.Result StateOnlyAttemptSecrets ProverRwRngCaller.Error)
    (hr : selected_callback policy p n k = .ok out) :
    ∃ nonce afterNonce afterTape nativeStatus,
      policy.call_mut n k = .ok (nonce,afterNonce) ∧
      StateOnlyAttemptSecrets.generate_with Tape.Insts.Prover_rw_rng_callerDraw64 nonce p =
        .ok (afterTape,nativeStatus) ∧
      out = (afterTape,afterNonce,mapped nativeStatus) := by
  cases hp : policy.call_mut n k with
  | fail e => simp only [selected_callback,hp,bind_tc_fail] at hr; cases hr
  | div => simp only [selected_callback,hp,bind_tc_div] at hr; cases hr
  | ok pair =>
    rcases pair with ⟨nonce,afterNonce⟩
    cases he : StateOnlyAttemptSecrets.generate_with Tape.Insts.Prover_rw_rng_callerDraw64 nonce p with
    | fail e =>
      simp only [selected_callback,hp,bind_tc_ok,Aeneas.Std.uncurry,he,bind_tc_fail] at hr
      cases hr
    | div =>
      simp only [selected_callback,hp,bind_tc_ok,Aeneas.Std.uncurry,he,bind_tc_div] at hr
      cases hr
    | ok result =>
      rcases result with ⟨afterTape,nativeStatus⟩
      have same := callback_step policy p afterTape n afterNonce k nonce nativeStatus hp he
      exact ⟨nonce,afterNonce,afterTape,nativeStatus,rfl,he,Result.ok.inj (hr.symm.trans same)⟩

theorem ordered_indices {N L B : Type} {policy : Policy N} {body : Body B L}
    {s : State N L B} {states out} (path : Replay policy body s states out) :
    states.map (fun t => t.2.2.2.2.val) = List.range' s.2.2.2.2.val states.length := by
  induction path with
  | done h => simp
  | @cont s next states out h path ih =>
    have prog := step_progress policy body s.1 s.2.1 s.2.2.1 s.2.2.2.1 s.2.2.2.2 next h
    simp only [List.map_cons,List.length_cons,List.range'_succ,ih,prog.2]

#print axioms callback_invocation
#print axioms ordered_indices
end R1Z.ProverRwRngCallerEvents
