import NNH_AuthLaneCut
import NNH_LaneOk
import NNH_AuthMasterInputs
import NNH_AuthResult
set_option autoImplicit false
noncomputable section
namespace NNH_AuthLaneInputs
open Aeneas Aeneas.Std AdapterRw NND_Carrier NNH_ModelCarrier NNH_Libraries
attribute [local instance] Classical.propDecidable

structure Packet (base : Ops) (env : RSL.Env) (pool : solana_pubkey.Pubkey)
 (m c l : r1_pool_adapter.owned.OwnedAccount) (id : U8)
 (master : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
 (ck : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestCheckpointV1) (out : RSL.Authenticated) where
 data : Slice U8
 read : r1_pool_adapter.owned.OwnedAccount.data (NNH_Tx2ModelSlots.install base env) l=.ok (.Ok data)
 state : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestLaneStateV1
 decode : NNH_LaneModel.decode data=.ok (.Ok state)
 pool_eq : state.master=m.key
 lane_eq : state.lane_id=id
 pda : (NNH_Tx2ModelSlots.install base env).op38 (NNH_AuthSeeds.lane m.key id state.bump) pool=.ok (.Ok l.key)
 output : auth (NNH_AuthResult.value master ck state m.key c.key l.key)=out

theorem produce (base : Ops) (env : RSL.Env) (program pool : solana_pubkey.Pubkey)
 (p m c l r e v : r1_pool_adapter.owned.OwnedAccount) (id : U8) (slot : U64)
 (master : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
 (ck : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestCheckpointV1) (out : RSL.Authenticated)
 (success : NNH_AuthTailValues.laneValue L D
  ⟨key program,[account p,account m,account c,account l,account r,account e,account v],key pool,byte id,NND_Carrier.slot slot⟩
  (account p) (account m) (account c) (account l) (account r) (account e) (account v) env (NND_Carrier.master master) (NND_Carrier.checkpoint ck)=.ok out) :
 Nonempty (Packet base env pool m c l id master ck out) := by
 obtain ⟨cut⟩ := NNH_AuthLaneCut.produce _ _ _ _ _ _ _ _ _ _ _ _ _ _ success
 rcases cut with ⟨bs,data_ok,state,decode_ok,guard_ok,pda_ok,output⟩
 have read := NNH_AuthGuardPorts.data base env l
 rw [data_ok] at read
 obtain ⟨data,read,data_eq⟩ := NNH_MappedOk.value _ _ _ read
 rw [←data_eq] at decode_ok
 obtain ⟨native,decode,native_eq⟩ := NNH_LaneOk.value data state decode_ok
 subst state
 simp only [Bool.or_eq_false_iff,decide_eq_false_iff_not,not_not,bne_eq_false_iff_eq] at guard_ok
 have pool_eq : native.master=m.key := (key_eq_iff _ _).mp guard_ok.1
 have lane_eq : native.lane_id=id := (byte_eq_iff _ _).mp guard_ok.2
 have pda : (NNH_Tx2ModelSlots.install base env).op38 (NNH_AuthSeeds.lane m.key id native.bump) pool=.ok (.Ok l.key) := by
  apply NNH_PdaOk.native
  rw [NNH_AuthSeeds.lane_bytes]
  exact pda_ok
 exact ⟨⟨data,read,native,decode,pool_eq,lane_eq,pda,(NNH_AuthResult.carrier master ck native m.key c.key l.key).trans output.symm⟩⟩
#print axioms produce
end NNH_AuthLaneInputs
