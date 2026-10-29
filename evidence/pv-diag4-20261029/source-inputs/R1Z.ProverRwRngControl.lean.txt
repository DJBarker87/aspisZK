import R1Z.ProverRwRngNonzero

/-! Direct emitted-owner control under explicit primitive replies. No native
provider, OS law, whole-owner equivalence or drop contract is assumed. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwRngControl
open Aeneas Aeneas.Std Result ControlFlow ProverRwRng
variable [ErasureFns]
abbrev Status := core.result.Result StateOnlyAttemptSecrets StateOnlyAttemptEntropyError
abbrev body {P : Type} := @StateOnlyAttemptSecrets.generate_with_loop.body _ P
abbrev ownerLoop {P : Type} := @StateOnlyAttemptSecrets.generate_with_loop _ P

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
    zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,bind_tc_ok,Aeneas.Std.uncurry,reply]
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
  rw [ProverRwRngNonzero.nonzero_repeat byte stable initial]
  simp only [bind_tc_ok]
  split <;> simp_all only [bind_tc_ok,if_true,if_false]

theorem error_state {P : Type} (draw : Draw64 P) (p after : P)
    (nonce : Array U8 32#usize) (retry limit : Usize) (below : retry < limit)
    (written : Array U8 64#usize) (error : U8)
    (reply : draw.fill p (Array.repeat 64#usize 0#u8) = .ok ((after,.Err error),written)) :
    body draw nonce limit p retry = .ok (.done (after,.Err (.Os error))) := by
  unfold body StateOnlyAttemptSecrets.generate_with_loop.body
  simp only [below,if_true,zeroize.Zeroizing.new,
    zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,bind_tc_ok,Aeneas.Std.uncurry,reply]

theorem cap_state {P : Type} (draw : Draw64 P) (p : P)
    (nonce : Array U8 32#usize) (retry limit : Usize) (stop : ¬ retry < limit) :
    body draw nonce limit p retry = .ok (.done (p,.Err .RepeatedZeroBlock)) := by
  simp only [body,StateOnlyAttemptSecrets.generate_with_loop.body,stop,if_false]

#print axioms constant_step
#print axioms error_state
#print axioms cap_state
end R1Z.ProverRwRngControl
