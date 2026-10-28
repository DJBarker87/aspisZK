import R1Z.ProverRwEffectRegression
import R1Z.ProverRwEffectControl

/-! Full entropy-owner control, with the source nonce check retained. The pure
specialization is an exact extraction theorem. The world interpretation is a
candidate awaiting effect adequacy, not a new extraction trust assumption. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwEffectOwner
open Aeneas Aeneas.Std Result ControlFlow ProverRwFull
open ProverRwEffectSource ProverRwEffectTape
variable [ExternalTypes] [ExternalFuns]

def pureOwner (nonce : Array U8 32#usize) : Result Status := do
  let b ← aspis_prover.state_only_entropy.entropy_nonzero32 nonce
  if b then
    loop (fun retry => pure (emit nonce aspis_prover.state_only_entropy.ENTROPY_RETRY_LIMIT retry)) 0#usize
  else .ok (.Err .RepeatedZeroBlock)

theorem pure_owner_eq (nonce : Array U8 32#usize) :
    pureOwner nonce =
      aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.generate_for_mask_nonce nonce := by
  have steps : (fun retry => pure (emit nonce aspis_prover.state_only_entropy.ENTROPY_RETRY_LIMIT retry)) =
      (fun retry => aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.generate_for_mask_nonce_loop.body
        nonce aspis_prover.state_only_entropy.ENTROPY_RETRY_LIMIT retry) := by
    funext retry
    exact pure_eq nonce _ retry
  unfold pureOwner aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.generate_for_mask_nonce
    aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.generate_for_mask_nonce_loop
  rw [steps]

/-- 16 entered draws plus the source's terminal cap test. A missing finite
reply remains a request boundary; it is never mapped to verifier.Error.Entropy. -/
def worldOwner (nonce : Array U8 32#usize) (world : World) : Execution :=
  match aspis_prover.state_only_entropy.entropy_nonzero32 nonce with
  | .fail e => ⟨.returned (.fail e),world⟩
  | .div => ⟨.returned .div,world⟩
  | .ok false => ⟨.returned (.ok (.Err .RepeatedZeroBlock)),world⟩
  | .ok true => run nonce aspis_prover.state_only_entropy.ENTROPY_RETRY_LIMIT 17 0#usize world

theorem rejected_nonce (nonce : Array U8 32#usize)
    (h : aspis_prover.state_only_entropy.entropy_nonzero32 nonce = .ok false) (world : World) :
    worldOwner nonce world = ⟨.returned (.ok (.Err .RepeatedZeroBlock)),world⟩ := by
  simp only [worldOwner,h]

theorem owner_tape (nonce : Array U8 32#usize) (world : World) :
    (worldOwner nonce world).world.reads.map Prod.snd ++ (worldOwner nonce world).world.tape =
      world.reads.map Prod.snd ++ world.tape := by
  unfold worldOwner
  cases aspis_prover.state_only_entropy.entropy_nonzero32 nonce with
  | fail e => rfl
  | div => rfl
  | ok b => cases b with
    | false => rfl
    | true => exact run_tape nonce _ _ _ world

/-- Full source-owner regression with an admitted nonzero public nonce. -/
theorem owner_zero_then_one (ops : ExternalFuns) (rest : List (Result Reply))
    (reads : List (Slice U8 × Result Reply)) :
    letI : ExternalFuns := ProverRwEffectPrefix.install ops
    let nonce := Array.repeat 32#usize 1#u8
    let zero := ProverRwEntropyObstruction.zeroInput
    let one := ProverRwEntropyObstruction.oneOutput
    let r0 : Result Reply := .ok (.Ok (),zero)
    let r1 : Result Reply := .ok (.Ok (),one)
    worldOwner nonce ⟨r0::r1::rest,reads⟩ =
      ⟨.returned (.ok (.Ok ⟨nonce,Array.repeat 32#usize 1#u8,Array.repeat 32#usize 1#u8⟩)),
        ⟨rest,reads ++ [(zero,r0),(zero,r1)]⟩⟩ := by
  letI : ExternalFuns := ProverRwEffectPrefix.install ops
  dsimp only
  unfold worldOwner
  rw [ProverRwEffectNonzero.nonzero_repeat 1#u8 (by rfl) (by rfl)]
  simp only [show (1#u8 != 0#u8) = true from by decide]
  simp only [aspis_prover.state_only_entropy.ENTROPY_RETRY_LIMIT]
  change run (Array.repeat 32#usize 1#u8) 16#usize 17 0#usize _ = _
  simp only [run,step,
    ProverRwEffectPrefix.request ops (Array.repeat 32#usize 1#u8) 16#usize 0#usize (by decide),resumeResult,
    bind_tc_ok,ProverRwEffectRegression.after_zero,finish,advance,
    ProverRwEffectRegression.add_zero_one,
    ProverRwEffectPrefix.request ops (Array.repeat 32#usize 1#u8) 16#usize 1#usize (by decide),
    ProverRwEffectRegression.after_one,List.append_assoc]
  rfl

#print axioms pure_owner_eq
#print axioms rejected_nonce
#print axioms owner_tape
#print axioms owner_zero_then_one
end R1Z.ProverRwEffectOwner
