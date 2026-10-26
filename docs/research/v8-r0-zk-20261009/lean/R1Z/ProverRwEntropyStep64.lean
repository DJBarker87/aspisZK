import R1Z.ProverRwEntropyDecode64
import R1Z.ProverRwEntropyNonceGuard64
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwEntropyStep64
open Aeneas Aeneas.Std Result ControlFlow ProverRwFull
open ProverRwEffectSource ProverRwEffectTape ProverRwEffectPrefix
variable [ExternalTypes]
attribute [local instance] Classical.propDecidable

/-- No per-reply continuation/decoder equation is assumed. The advanced
world retains the complete ordered fill request and this full reply. -/
theorem full (ops : ExternalFuns) (nonce : Array U8 32#usize) (limit retry : Usize)
    (below : retry < limit) (bytes : Array U8 64#usize)
    (rest : List (Result Reply)) (reads : List (Slice U8 × Result Reply)) :
    letI : ExternalFuns := install ops
    let reply : Result Reply := .ok (.Ok (),Array.to_slice bytes)
    step nonce limit retry ⟨reply::rest,reads⟩ =
      ⟨if ProverCommitPublicNonce40.decode (ProverRwEntropyDecode64.raw bytes) = none then
          .retry (Usize.wrapping_add retry 1#usize)
        else .returned (.ok (.Ok ⟨nonce,ProverRwEntropyDecode64.field bytes,ProverRwEntropyDecode64.leaf bytes⟩)),
       ⟨rest,reads ++ [(ProverRwEntropyObstruction.zeroInput,reply)]⟩⟩ := by
  letI : ExternalFuns := install ops
  dsimp only
  unfold step
  rw [request ops nonce limit retry below]
  simp only [resumeResult,bind_tc_ok,ProverRwEntropyDecode64.after_full,advance]
  split <;> rfl

theorem failed (ops : ExternalFuns) (nonce : Array U8 32#usize) (limit retry : Usize)
    (below : retry < limit) (error : Error) (rest : List (Result Reply))
    (reads : List (Slice U8 × Result Reply)) :
    letI : ExternalFuns := install ops
    step nonce limit retry ⟨.fail error::rest,reads⟩ =
      ⟨.returned (.fail error),⟨rest,reads ++ [(ProverRwEntropyObstruction.zeroInput,.fail error)]⟩⟩ := by
  letI : ExternalFuns := install ops
  unfold step
  rw [request ops nonce limit retry below]
  rfl

theorem diverged (ops : ExternalFuns) (nonce : Array U8 32#usize) (limit retry : Usize)
    (below : retry < limit) (rest : List (Result Reply))
    (reads : List (Slice U8 × Result Reply)) :
    letI : ExternalFuns := install ops
    step nonce limit retry ⟨.div::rest,reads⟩ =
      ⟨.returned .div,⟨rest,reads ++ [(ProverRwEntropyObstruction.zeroInput,.div)]⟩⟩ := by
  letI : ExternalFuns := install ops
  unfold step
  rw [request ops nonce limit retry below]
  rfl

theorem after_os (ops : ExternalFuns) (nonce : Array U8 32#usize) (retry : Usize)
    (error : getrandom.error.Error) (bytes : Slice U8) :
    @after _ (install ops) nonce retry back (.Err error,bytes) =
      .ok (.done (.Err (.Os error))) := by
  unfold after
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
    aspis_prover.state_only_entropy.StateOnlyAttemptEntropyError.Insts.CoreConvertFromError,
    aspis_prover.state_only_entropy.StateOnlyAttemptEntropyError.Insts.CoreConvertFromError.from]
  rfl

theorem os (ops : ExternalFuns) (nonce : Array U8 32#usize) (limit retry : Usize)
    (below : retry < limit) (error : getrandom.error.Error) (bytes : Slice U8)
    (rest : List (Result Reply)) (reads : List (Slice U8 × Result Reply)) :
    letI : ExternalFuns := install ops
    let reply : Result Reply := .ok (.Err error,bytes)
    step nonce limit retry ⟨reply::rest,reads⟩ =
      ⟨.returned (.ok (.Err (.Os error))),
       ⟨rest,reads ++ [(ProverRwEntropyObstruction.zeroInput,reply)]⟩⟩ := by
  letI : ExternalFuns := install ops
  dsimp only
  unfold step
  rw [request ops nonce limit retry below]
  simp only [resumeResult,bind_tc_ok,after_os]
  rfl

theorem cap (ops : ExternalFuns) (nonce : Array U8 32#usize) (limit retry : Usize)
    (finished : ¬ retry < limit) (world : World) :
    letI : ExternalFuns := install ops
    step nonce limit retry world = ⟨.returned (.ok (.Err .RepeatedZeroBlock)),world⟩ := by
  letI : ExternalFuns := install ops
  unfold step emit
  rw [if_neg finished]
  rfl

theorem unserved (ops : ExternalFuns) (nonce : Array U8 32#usize) (limit retry : Usize)
    (below : retry < limit) (reads : List (Slice U8 × Result Reply)) :
    letI : ExternalFuns := install ops
    step nonce limit retry ⟨[],reads⟩ =
      ⟨.request ProverRwEntropyObstruction.zeroInput (after nonce retry back),⟨[],reads⟩⟩ := by
  letI : ExternalFuns := install ops
  unfold step
  rw [request ops nonce limit retry below]

#print axioms after_os
#print axioms os
#print axioms cap
#print axioms unserved
#print axioms full
#print axioms failed
#print axioms diverged
end R1Z.ProverRwEntropyStep64
