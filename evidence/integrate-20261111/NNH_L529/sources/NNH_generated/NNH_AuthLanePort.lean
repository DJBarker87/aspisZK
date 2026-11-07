import NNH_AuthLaneInputs
import NNH_AuthLaneStep
set_option autoImplicit false
noncomputable section
namespace NNH_AuthLanePort
open Aeneas Aeneas.Std AdapterRw NND_Carrier NNH_ModelCarrier NNH_Libraries

theorem value (base : Ops) (env : RSL.Env) (program pool : solana_pubkey.Pubkey)
 (p m c l r e v : r1_pool_adapter.owned.OwnedAccount) (id : U8) (slot : U64)
 (master : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
 (ck : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestCheckpointV1) (out : RSL.Authenticated)
 (success : NNH_AuthTailValues.laneValue L D
  ⟨key program,[account p,account m,account c,account l,account r,account e,account v],key pool,byte id,NND_Carrier.slot slot⟩
  (account p) (account m) (account c) (account l) (account r) (account e) (account v) env (NND_Carrier.master master) (NND_Carrier.checkpoint ck)=.ok out) :
 ∃ native, NNH_AuthTailParts.lane (NNH_Tx2ModelSlots.install base env) program m c l r e pool id slot m.key master ck c.key=.ok (.Ok native) ∧ auth native=out := by
 obtain ⟨packet⟩ := NNH_AuthLaneInputs.produce base env program pool p m c l r e v id slot master ck out success
 exact ⟨_,NNH_AuthLaneStep.source base env program pool m c l r e id slot master ck packet.data packet.state packet.read packet.decode packet.pool_eq packet.lane_eq packet.pda,packet.output⟩
#print axioms value
end NNH_AuthLanePort
