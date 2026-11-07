import NNH_AuthCheckpointCut
import NNH_AuthMasterInputs
import NNH_CheckpointSeeds
set_option autoImplicit false
noncomputable section
namespace NNH_AuthCheckpointInputs
open Aeneas Aeneas.Std AdapterRw NND_Carrier NNH_ModelCarrier NNH_Libraries
attribute [local instance] Classical.propDecidable

structure Packet (base : Ops) (env : RSL.Env) (program pool : solana_pubkey.Pubkey)
 (p m c l r e v : r1_pool_adapter.owned.OwnedAccount) (lane : U8) (slot : U64)
 (master : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1) (out : RSL.Authenticated) where
 data : Slice U8
 read : r1_pool_adapter.owned.OwnedAccount.data (NNH_Tx2ModelSlots.install base env) c=.ok (.Ok data)
 checkpoint : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestCheckpointV1
 decode : NKF_CheckpointBox.reference data=.ok (.Ok checkpoint)
 pool_eq : checkpoint.master=m.key
 domain_eq : checkpoint.deployment_domain=master.identity.deployment_domain
 pda : (NNH_Tx2ModelSlots.install base env).op38 (NNH_AuthSeeds.checkpoint m.key checkpoint.checkpoint_sequence checkpoint.bump) pool=.ok (.Ok c.key)
 next : NNH_AuthTailValues.laneValue L D
  ⟨key program,[account p,account m,account c,account l,account r,account e,account v],key pool,byte lane,NND_Carrier.slot slot⟩
  (account p) (account m) (account c) (account l) (account r) (account e) (account v) env (NND_Carrier.master master) (NND_Carrier.checkpoint checkpoint)=.ok out

theorem produce (base : Ops) (env : RSL.Env) (program pool : solana_pubkey.Pubkey)
 (p m c l r e v : r1_pool_adapter.owned.OwnedAccount) (lane : U8) (slot : U64)
 (master : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1) (out : RSL.Authenticated)
 (success : NNH_AuthTailValues.checkpointValue L D
  ⟨key program,[account p,account m,account c,account l,account r,account e,account v],key pool,byte lane,NND_Carrier.slot slot⟩
  (account p) (account m) (account c) (account l) (account r) (account e) (account v) env (NND_Carrier.master master)=.ok out) :
 Nonempty (Packet base env program pool p m c l r e v lane slot master out) := by
 obtain ⟨cut⟩ := NNH_AuthCheckpointCut.produce _ _ _ _ _ _ _ _ _ _ _ _ _ success
 rcases cut with ⟨bs,data_ok,checkpoint,decode_ok,guard_ok,pda_ok,next_ok⟩
 have read := NNH_AuthGuardPorts.data base env c
 rw [data_ok] at read
 obtain ⟨data,read,data_eq⟩ := NNH_MappedOk.value _ _ _ read
 rw [←data_eq] at decode_ok
 obtain ⟨native,decode,native_eq⟩ := NNH_BoxOk.checkpoint data checkpoint decode_ok
 subst checkpoint
 simp only [Bool.or_eq_false_iff,decide_eq_false_iff_not,not_not] at guard_ok
 have pool_eq : native.master=m.key := (key_eq_iff _ _).mp guard_ok.1
 have domain_eq : native.deployment_domain=master.identity.deployment_domain := (key_eq_iff _ _).mp guard_ok.2
 have pda : (NNH_Tx2ModelSlots.install base env).op38 (NNH_AuthSeeds.checkpoint m.key native.checkpoint_sequence native.bump) pool=.ok (.Ok c.key) := by
  apply NNH_PdaOk.native
  rw [NNH_CheckpointSeeds.bytes]
  exact pda_ok
 exact ⟨⟨data,read,native,decode,pool_eq,domain_eq,pda,next_ok⟩⟩
#print axioms produce
end NNH_AuthCheckpointInputs
