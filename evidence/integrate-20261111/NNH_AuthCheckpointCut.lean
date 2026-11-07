import NNH_AuthMasterCut
set_option autoImplicit false
namespace NNH_AuthCheckpointCut
open RSL NND_Returned

structure Packet (L : PoolLib) (D : DeployedIds) (a : TX2_233.Args)
 (p m c l r e v : OwnedAccount) (env : Env) (master : Master) (out : Authenticated) where
 data : Bytes
 data_ok : c.bytes=.ok data
 checkpoint : Checkpoint
 decode_ok : L.decodeCheckpoint data=some checkpoint
 guard_ok : (decide (checkpoint.master ≠ m.key) || decide (checkpoint.deployment_domain ≠ master.identity.deployment_domain))=false
 pda_ok : env.pda [SEED_CHECKPOINT,m.key.bytes,u64le checkpoint.checkpoint_sequence,[checkpoint.bump]] a.pool_program=some c.key
 next_ok : NNH_AuthTailValues.laneValue L D a p m c l r e v env master checkpoint=.ok out

theorem produce (L : PoolLib) (D : DeployedIds) (a : TX2_233.Args)
 (p m c l r e v : OwnedAccount) (env : Env) (master : Master) (out : Authenticated)
 (success : NNH_AuthTailValues.checkpointValue L D a p m c l r e v env master=.ok out) :
 Nonempty (Packet L D a p m c l r e v env master out) := by
 unfold NNH_AuthTailValues.checkpointValue at success
 obtain ⟨data,data_ok,success⟩ := NNH_ValueOk.bind _ _ out success
 obtain ⟨checkpoint,decode,success⟩ := NNH_ValueOk.bind _ _ out success
 obtain ⟨guard,success⟩ := NNH_ValueOk.seq _ _ out success
 obtain ⟨guard_ok,pda_ok⟩ := NNH_PdaOk.guard _ _ _ _ _ guard
 exact ⟨⟨data,data_ok,checkpoint,NNH_OptionOk.value _ _ _ decode,guard_ok,pda_ok,success⟩⟩
#print axioms produce
end NNH_AuthCheckpointCut
