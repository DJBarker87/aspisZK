import R1Z.ProverRwRngNonzero
import R1Z.ProverRwRngCallerControl

/-! Direct emitted-owner control under explicit primitive replies. No native
provider, OS law, whole-owner equivalence or drop contract is assumed. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwRngCallerEntropy
open Aeneas Aeneas.Std Result ControlFlow ProverRwRngCaller
variable [NativeTypes] [ErasureFns]
abbrev Status := core.result.Result StateOnlyAttemptSecrets StateOnlyAttemptEntropyError
abbrev body {P : Type} := @StateOnlyAttemptSecrets.generate_with_loop.body _ _ P
abbrev ownerLoop {P : Type} := @StateOnlyAttemptSecrets.generate_with_loop _ _ P

theorem scan_same (nonce : Array U8 32#usize) :
    entropy_nonzero32 nonce = ProverRwRng.entropy_nonzero32 nonce := rfl

theorem constant_step {P : Type} (draw : Draw64 P) (p after : P)
    (nonce : Array U8 32#usize) (retry limit : Usize) (below : retry < limit)
    (byte : U8) (stable : byte ||| byte = byte) (initial : (0#u8) ||| byte = byte)
    (reply : draw.fill p (Array.repeat 64#usize 0#u8) =
      .ok ((after,.Ok ()),Array.repeat 64#usize byte)) :
    body draw nonce limit p retry =
      if byte != 0#u8 then
        .ok (.done (after,.Ok ⟨nonce,Array.repeat 32#usize byte,Array.repeat 32#usize byte⟩))
      else (do
        let nextRetry ← retry + 1#usize
        .ok (.cont (after,nextRetry))) := by
  unfold body StateOnlyAttemptSecrets.generate_with_loop.body
  simp only [below,if_true,zeroize.Zeroizing.new,
    zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,bind_tc_ok,Aeneas.Std.uncurry,reply,StateOnlyAttemptEntropyError.Insts.CoreConvertFromError.from]
  change (do
    let b ← entropy_nonzero32 (Array.repeat 32#usize byte)
    if b then do
      let b1 ← entropy_nonzero32 (Array.repeat 32#usize byte)
      if b1 then .ok (.done (after,.Ok ⟨nonce,Array.repeat 32#usize byte,Array.repeat 32#usize byte⟩))
      else (do
        let nextRetry ← retry + 1#usize
        .ok (.cont (after,nextRetry)))
    else (do
        let nextRetry ← retry + 1#usize
        .ok (.cont (after,nextRetry))) : Result (ControlFlow (P × Usize) (P × Status))) = _
  letI : ProverRwRng.ErasureFns :=
    { scalar := fun _ z => .ok z, array := fun _ z => .ok z }
  rw [scan_same, ProverRwRngNonzero.nonzero_repeat byte stable initial]
  simp only [bind_tc_ok]
  split <;> simp_all only [bind_tc_ok,if_true,if_false]

theorem error_state {P : Type} (draw : Draw64 P) (p after : P)
    (nonce : Array U8 32#usize) (retry limit : Usize) (below : retry < limit)
    (written : Array U8 64#usize) (error : getrandom.error.Error)
    (reply : draw.fill p (Array.repeat 64#usize 0#u8) = .ok ((after,.Err error),written)) :
    body draw nonce limit p retry = .ok (.done (after,.Err (.Os error))) := by
  unfold body StateOnlyAttemptSecrets.generate_with_loop.body
  simp only [below,if_true,zeroize.Zeroizing.new,
    zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,bind_tc_ok,Aeneas.Std.uncurry,reply,StateOnlyAttemptEntropyError.Insts.CoreConvertFromError.from]

theorem cap_state {P : Type} (draw : Draw64 P) (p : P)
    (nonce : Array U8 32#usize) (retry limit : Usize) (stop : ¬ retry < limit) :
    body draw nonce limit p retry = .ok (.done (p,.Err .RepeatedZeroBlock)) := by
  simp only [body,StateOnlyAttemptSecrets.generate_with_loop.body,stop,if_false]

theorem zero_then_one_loop {P : Type} (draw : Draw64 P) (p0 p1 p2 : P)
    (nonce : Array U8 32#usize)
    (first : draw.fill p0 (Array.repeat 64#usize 0#u8) =
      .ok ((p1,.Ok ()),Array.repeat 64#usize 0#u8))
    (second : draw.fill p1 (Array.repeat 64#usize 0#u8) =
      .ok ((p2,.Ok ()),Array.repeat 64#usize 1#u8)) :
    StateOnlyAttemptSecrets.generate_with_loop draw nonce p0 16#usize 0#usize =
      .ok (p2,.Ok ⟨nonce,Array.repeat 32#usize 1#u8,Array.repeat 32#usize 1#u8⟩) := by
  have zero := constant_step draw p0 p1 nonce 0#usize 16#usize (by decide)
    0#u8 (by rfl) (by rfl) first
  have one := constant_step draw p1 p2 nonce 1#usize 16#usize (by decide)
    1#u8 (by rfl) (by rfl) second
  have add : ((0#usize) + 1#usize : Result Usize) = .ok (1#usize) := by
    rw [ProverRwSamplerArithmetic.add_exact 0#usize 1#usize (by scalar_tac)]
    apply congrArg Result.ok
    apply UScalar.eq_of_val_eq
    rw [Usize.wrapping_add_val_eq]
    change 1 % UScalar.size .Usize = 1
    exact Nat.mod_eq_of_lt (1#usize).hSize
  simp only [show (0#u8 != 0#u8) = false from rfl,Bool.false_eq_true,if_false,add,bind_tc_ok] at zero
  simp only [show (1#u8 != 0#u8) = true from rfl,if_true] at one
  let step : P × Usize → Result (ControlFlow (P × Usize) (P × Status)) :=
    fun state => body draw nonce 16#usize state.1 state.2
  change loop step (p0,0#usize) = _
  rw [loop]
  simp only [step,zero,bind_tc_ok]
  rw [loop]
  simp only [step,one,bind_tc_ok]


theorem zero_then_one_owner (p0 p1 p2 : Tape) (nonce : Array U8 32#usize)
    (admitted : entropy_nonzero32 nonce = .ok true)
    (first : Tape.Insts.Prover_rw_rng_callerDraw64.fill p0 (Array.repeat 64#usize 0#u8) =
      .ok ((p1,.Ok ()),Array.repeat 64#usize 0#u8))
    (second : Tape.Insts.Prover_rw_rng_callerDraw64.fill p1 (Array.repeat 64#usize 0#u8) =
      .ok ((p2,.Ok ()),Array.repeat 64#usize 1#u8)) :
    StateOnlyAttemptSecrets.generate_with Tape.Insts.Prover_rw_rng_callerDraw64 nonce p0 =
      .ok (p2,.Ok ⟨nonce,Array.repeat 32#usize 1#u8,Array.repeat 32#usize 1#u8⟩) := by
  unfold StateOnlyAttemptSecrets.generate_with
  rw [admitted]
  simp only [bind_tc_ok,if_true,ENTROPY_RETRY_LIMIT]
  exact zero_then_one_loop _ _ _ _ _ first second

#print axioms scan_same
#print axioms constant_step
#print axioms error_state
#print axioms cap_state
#print axioms zero_then_one_loop
#print axioms zero_then_one_owner
end R1Z.ProverRwRngCallerEntropy
