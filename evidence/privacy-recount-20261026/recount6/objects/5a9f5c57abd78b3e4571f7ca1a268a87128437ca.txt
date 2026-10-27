import R1Z.ProverRwRngCallerEntropy
import R1Z.ProverRwRngCallerReplay
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwRngCallerComposition
open Aeneas Aeneas.Std Result ControlFlow ProverRwRngCaller
open ProverRwRngCallerControl ProverRwRngCallerEntropy
variable [NativeTypes] [ErasureFns]

theorem one_owner (p p' : Tape) (nonce : Array U8 32#usize)
    (admitted : entropy_nonzero32 nonce = .ok true)
    (reply : Tape.Insts.Prover_rw_rng_callerDraw64.fill p (Array.repeat 64#usize 0#u8) =
      .ok ((p',.Ok ()),Array.repeat 64#usize 1#u8)) :
    StateOnlyAttemptSecrets.generate_with Tape.Insts.Prover_rw_rng_callerDraw64 nonce p =
      .ok (p',.Ok ⟨nonce,Array.repeat 32#usize 1#u8,Array.repeat 32#usize 1#u8⟩) := by
  have step := constant_step Tape.Insts.Prover_rw_rng_callerDraw64 p p' nonce
    0#usize 16#usize (by decide) 1#u8 (by rfl) (by rfl) reply
  simp only [show (1#u8 != 0#u8) = true from rfl,if_true] at step
  unfold StateOnlyAttemptSecrets.generate_with
  rw [admitted]
  simp only [bind_tc_ok,if_true,ENTROPY_RETRY_LIMIT]
  unfold StateOnlyAttemptSecrets.generate_with_loop
  rw [loop]
  simpa only [step,bind_tc_ok] using step

theorem zero_reject_fatal {N L B : Type} (policy : Policy N) (body : Body B L)
    (p0 p1 p2 p3 : Tape) (n0 n1 n2 : N) (l0 l1 l2 : L) (b0 b1 b2 : B)
    (nonce0 nonce1 : Array U8 32#usize)
    (policy0 : policy.call_mut n0 0#usize = .ok (nonce0,n1))
    (policy1 : policy.call_mut n1 1#usize = .ok (nonce1,n2))
    (admit0 : entropy_nonzero32 nonce0 = .ok true)
    (admit1 : entropy_nonzero32 nonce1 = .ok true)
    (draw0 : Tape.Insts.Prover_rw_rng_callerDraw64.fill p0 (Array.repeat 64#usize 0#u8) =
      .ok ((p1,.Ok ()),Array.repeat 64#usize 0#u8))
    (draw1 : Tape.Insts.Prover_rw_rng_callerDraw64.fill p1 (Array.repeat 64#usize 0#u8) =
      .ok ((p2,.Ok ()),Array.repeat 64#usize 1#u8))
    (draw2 : Tape.Insts.Prover_rw_rng_callerDraw64.fill p2 (Array.repeat 64#usize 0#u8) =
      .ok ((p3,.Ok ()),Array.repeat 64#usize 1#u8))
    (body0 : body.call_mut b0
      (⟨nonce0,Array.repeat 32#usize 1#u8,Array.repeat 32#usize 1#u8⟩,l0) =
        .ok ((l1,.Err .Rejected),b1))
    (body1 : body.call_mut b1
      (⟨nonce1,Array.repeat 32#usize 1#u8,Array.repeat 32#usize 1#u8⟩,l1) =
        .ok ((l2,.Err .Semantic),b2)) :
    prove_masked_retrying_with policy body true p0 n0 l0 b0 =
      .ok (p3,n2,l2,b2,.Err .Semantic) := by
  have entropy0 := zero_then_one_owner p0 p1 p2 nonce0 admit0 draw0 draw1
  have entropy1 := one_owner p2 p3 nonce1 admit1 draw2
  have callback0 := callback_step policy p0 p2 n0 n1 0#usize nonce0 _ policy0 entropy0
  have callback1 := callback_step policy p2 p3 n1 n2 1#usize nonce1 _ policy1 entropy1
  have increment : ((0#usize) + 1#usize : Result Usize) = .ok (1#usize) := by
    obtain ⟨next,h,hval⟩ := increment_safe 0#usize (by decide)
    have same : next = 1#usize := by apply UScalar.eq_of_val_eq; exact hval
    simpa only [same] using h
  change retry_attempt policy body p0 n0 l0 b0 0#usize = _
  rw [body_rejected policy body p0 p2 n0 n1 l0 l1 b0 b1 0#usize 1#usize
    (by decide) _ callback0 body0 increment]
  exact body_fatal policy body p2 p3 n1 n2 l1 l2 b1 b2 1#usize
    (by decide) _ .Semantic (by intro h; cases h) callback1 body1

#print axioms one_owner
#print axioms zero_reject_fatal
end R1Z.ProverRwRngCallerComposition
