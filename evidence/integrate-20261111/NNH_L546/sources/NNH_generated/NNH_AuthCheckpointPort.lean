import NNH_AuthCheckpointInputs
import NNH_AuthCheckpointStep
import NNH_AuthLanePort
set_option autoImplicit false
noncomputable section
namespace NNH_AuthCheckpointPort
open Aeneas Aeneas.Std AdapterRw NND_Carrier NNH_ModelCarrier NNH_Libraries

theorem value (base : Ops) (env : RSL.Env) (program pool : solana_pubkey.Pubkey)
 (p m c l r e v : r1_pool_adapter.owned.OwnedAccount) (lane : U8) (slot : U64)
 (master : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1) (out : RSL.Authenticated)
 (success : NNH_AuthTailValues.checkpointValue L D
  ⟨key program,[account p,account m,account c,account l,account r,account e,account v],key pool,byte lane,NND_Carrier.slot slot⟩
  (account p) (account m) (account c) (account l) (account r) (account e) (account v) env (NND_Carrier.master master)=.ok out) :
 ∃ native,NNH_AuthTailParts.checkpoint (NNH_Tx2ModelSlots.install base env) program m c l r e pool lane slot m.key master=.ok (.Ok native) ∧ auth native=out := by
 obtain ⟨packet⟩ := NNH_AuthCheckpointInputs.produce base env program pool p m c l r e v lane slot master out success
 obtain ⟨native,run,output⟩ := NNH_AuthLanePort.value base env program pool p m c l r e v lane slot master packet.checkpoint out packet.next
 refine ⟨native,?_,output⟩
 rw [NNH_AuthCheckpointStep.source base env program pool m c l r e lane slot master packet.data packet.checkpoint packet.read packet.decode packet.pool_eq packet.domain_eq packet.pda]
 exact run
#print axioms value
end NNH_AuthCheckpointPort
