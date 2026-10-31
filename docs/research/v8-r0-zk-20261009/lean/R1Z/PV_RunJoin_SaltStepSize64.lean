import R1Z.PV_RunJoin_Vector44
import R1Z.PV_RunJoin_PostBind63
set_option autoImplicit false
namespace R1Z.PV_RunJoin_SaltStepSize64
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_ResultPost41
variable [ExternalTypes] [ExternalFuns]

theorem push {T : Type} (v : alloc.vec.Vec T) (x : T) :
    Post (fun next => next.length=v.length+1) (alloc.vec.Vec.push v x) := by
  unfold alloc.vec.Vec.push
  dsimp only
  split
  · change (v.val.concat x).length=v.val.length+1
    simp only [List.length_concat]
  · trivial

theorem step (reserved : aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets)
    (context : aspis_core.state_only_hiding.StateOnlyHidingContext)
    (hash : aspis_core.digest.LegacyHashFn) (tag : U8) (index : U32)
    (salts : alloc.vec.Vec (Array U8 32#usize)) :
    Post (fun status => match status with | .Err _ => True | .Ok next => next.length=salts.length+1)
      (prover.derive_private_salt_step reserved context hash tag index salts) := by
  unfold prover.derive_private_salt_step
  apply PV_RunJoin_ResultPost41.bind
  intro derived
  apply PV_RunJoin_ResultPost41.bind
  intro mapped
  cases mapped with
  | Err e => trivial
  | Ok salt =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
    apply PV_RunJoin_PostBind63.guarded _ _ _ _ (push salts salt)
    intro next hlen
    exact hlen

#print axioms push
#print axioms step
end R1Z.PV_RunJoin_SaltStepSize64
