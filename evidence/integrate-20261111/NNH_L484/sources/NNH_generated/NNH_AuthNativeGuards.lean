import NNH_AuthOkPrefix
import NNH_AuthGuardPorts
import NNH_DistinctPort
set_option autoImplicit false
noncomputable section
namespace NNH_AuthNativeGuards
open Aeneas Aeneas.Std AdapterRw NND_Carrier NNH_ModelCarrier

structure Packet (ops : Ops) (program pool : solana_pubkey.Pubkey)
 (p m c l r e v : r1_pool_adapter.owned.OwnedAccount) : Prop where
 proofGuard : r1_pool_adapter.owned.require_readonly_buffer p=.ok (.Ok ())
 checkpointGuard : r1_pool_adapter.owned.require_verifier_checkpoint ops v program false=.ok (.Ok ())
 masterGuard : r1_pool_adapter.owned.require_readonly_account ops m pool=.ok (.Ok ())
 checkpointOwner : r1_pool_adapter.owned.require_readonly_account ops c pool=.ok (.Ok ())
 laneGuard : r1_pool_adapter.owned.require_readonly_account ops l pool=.ok (.Ok ())
 distinctGuard : r1_pool_adapter.owned.require_distinct_accounts ops
  (Array.make 7#usize [p,m,c,l,r,e,v] (by rfl))=.ok (.Ok ())

theorem produce (L : RSL.PoolLib) (base : Ops) (env : RSL.Env) (program pool : solana_pubkey.Pubkey)
 (p m c l r e v : r1_pool_adapter.owned.OwnedAccount) (lane : UInt8) (slot : UInt64)
 (out : RSL.Authenticated)
 (success : NNH_AuthEval.bodyValue L LIB_Deployed.deployed
  ⟨key program,[account p,account m,account c,account l,account r,account e,account v],key pool,lane,slot⟩
  (account p) (account m) (account c) (account l) (account r) (account e) (account v) env=.ok out) :
 Packet (NNH_Tx2ModelSlots.install base env) program pool p m c l r e v := by
 have cut := NNH_AuthOkPrefix.produce _ _ _ _ _ _ _ _ _ _ _ _ success
 have proofGuard := NNH_AuthGuardPorts.buffer p
 rw [cut.proofGuard] at proofGuard
 have checkpointGuard := NNH_Tx2CheckpointPort.value base env v program false
 rw [cut.checkpointGuard] at checkpointGuard
 have masterGuard := NNH_AuthGuardPorts.readonly base env m pool
 rw [cut.masterGuard] at masterGuard
 have checkpointOwner := NNH_AuthGuardPorts.readonly base env c pool
 rw [cut.checkpointOwner] at checkpointOwner
 have laneGuard := NNH_AuthGuardPorts.readonly base env l pool
 rw [cut.laneGuard] at laneGuard
 refine ⟨NNH_MResultProjection.program_ok _ _ proofGuard,
  NNH_MResultProjection.program_ok _ _ checkpointGuard,
  NNH_MResultProjection.program_ok _ _ masterGuard,
  NNH_MResultProjection.program_ok _ _ checkpointOwner,
  NNH_MResultProjection.program_ok _ _ laneGuard,?_⟩
 apply NNH_DistinctPort.value base env _ (by decide)
 have distinct := cut.distinctGuard
 unfold RSL.requireDistinct at distinct
 split at distinct
 · rename_i h; exact h
 · cases distinct
#print axioms produce
end NNH_AuthNativeGuards
