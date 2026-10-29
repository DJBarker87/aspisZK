import R1Z.PV_RunJoin_NativeResultMap64
import R1Z.PV_RunJoin_LayoutConstants64
import R1Z.PV_RunJoin_Packets63
import R1Z.PV_RunJoin_SaltLoopSize64
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_NativeSaltSize64
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_NativeResidual63 PV_RunJoin_ResultPost41
attribute [local irreducible] opsNative PV_RunJoin_WeightInstalled46.selected

theorem count : aspis_core.r0.FIBRE_COUNT=ok 262144#usize := PV_RunJoin_LayoutConstants64.fibres

theorem source {S F : Type} (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (runtime : @PV_RunJoin_AllocatorWorld63.Runtime (types base) S F)
    (world : PV_FXM_ReserveWorld.World S F)
    (reserved : @aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets (types base))
    (context : aspis_core.state_only_hiding.StateOnlyHidingContext)
    (hash : aspis_core.digest.LegacyHashFn) (tag : U8) :
    Post (fun status => match status with | .Err _ => True | .Ok salts => salts.length=262144)
      (@prover.derive_private_salts (types base) (opsNative base heap box ops runtime world)
        reserved context hash tag) := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := opsNative base heap box ops runtime world
  unfold prover.derive_private_salts
  rw [count]
  simp only [bind_tc_ok]
  rw [PV_RunJoin_Packets63.reserve base heap box ops runtime world]
  simp only [bind_tc_ok,Aeneas.Std.uncurry]
  apply PV_RunJoin_ResultPost41.bind
  intro mapped
  cases mapped with
  | Err e => trivial
  | Ok unit =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
    have post := PV_RunJoin_SaltLoopSize64.complete reserved context hash tag 262144#usize
      (by decide) 262144 262144 (.Ok (alloc.vec.Vec.new (Array U8 32#usize))) 0#usize rfl rfl
    apply PV_RunJoin_PostBind63.guarded _ _ _ _ post
    intro status hstatus
    change Post _ ((opsNative base heap box ops runtime world).op11 _ status _)
    rw [PV_RunJoin_NativeResultMap64.complete]
    cases status with
    | Err e => trivial
    | Ok salts =>
      change salts.length=262144
      change salts.length+0=262144 at hstatus
      omega

theorem complete {S F : Type} (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base))
    (runtime : @PV_RunJoin_AllocatorWorld63.Runtime (types base) S F)
    (world : PV_FXM_ReserveWorld.World S F)
    (reserved : @aspis_prover.state_only_entropy.ReservedStateOnlyAttemptSecrets (types base))
    (context : aspis_core.state_only_hiding.StateOnlyHidingContext)
    (hash : aspis_core.digest.LegacyHashFn) (tag : U8) (salts : host_commitment.PrivateSalts)
    (success : @prover.derive_private_salts (types base) (opsNative base heap box ops runtime world)
      reserved context hash tag=ok (.Ok salts)) : salts.length=262144 :=
  PV_RunJoin_ResultPost41.success _ _ (.Ok salts) (source base heap box ops runtime world reserved context hash tag) success

#print axioms count
#print axioms source
#print axioms complete
end R1Z.PV_RunJoin_NativeSaltSize64
