import NNH_AuthTailValues
import NNH_PdaOk
set_option autoImplicit false
namespace NNH_AuthMasterCut
open RSL NND_Returned

structure Packet (L : PoolLib) (D : DeployedIds) (a : TX2_233.Args)
 (p m c l r e v : OwnedAccount) (env : Env) (out : Authenticated) where
 data : Bytes
 data_ok : m.bytes=.ok data
 master : Master
 decode_ok : L.decodeMaster data=some master
 guard_ok : (decide (master.identity.pool ≠ m.key) || master.initialized_lane_mask != ALL_LANES_MASK)=false
 pda_ok : env.pda [SEED_MASTER,master.identity.asset_mint.bytes,[master.bump]] a.pool_program=some m.key
 registry_ok : NNH_RegistryEval.value L D ⟨a.verifier_program,a.pool_program,m,master,r,e,a.current_slot⟩ env=.ok ()
 next_ok : NNH_AuthTailValues.checkpointValue L D a p m c l r e v env master=.ok out

theorem produce (L : PoolLib) (D : DeployedIds) (a : TX2_233.Args)
 (p m c l r e v : OwnedAccount) (env : Env) (out : Authenticated)
 (success : NNH_AuthTailValues.masterValue L D a p m c l r e v env=.ok out) :
 Nonempty (Packet L D a p m c l r e v env out) := by
 unfold NNH_AuthTailValues.masterValue at success
 obtain ⟨data,data_ok,success⟩ := NNH_ValueOk.bind _ _ out success
 obtain ⟨master,decode,success⟩ := NNH_ValueOk.bind _ _ out success
 obtain ⟨guard,success⟩ := NNH_ValueOk.seq _ _ out success
 obtain ⟨registry,success⟩ := NNH_ValueOk.seq _ _ out success
 obtain ⟨guard_ok,pda_ok⟩ := NNH_PdaOk.guard _ _ _ _ _ guard
 exact ⟨⟨data,data_ok,master,NNH_OptionOk.value _ _ _ decode,guard_ok,pda_ok,registry,success⟩⟩
#print axioms produce
end NNH_AuthMasterCut
