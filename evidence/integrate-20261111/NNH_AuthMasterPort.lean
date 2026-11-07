import NNH_AuthMasterInputs
import NNH_AuthMasterStep
import NNH_Tx2RegistryPort
set_option autoImplicit false
noncomputable section
namespace NNH_AuthMasterPort
open Aeneas Aeneas.Std AdapterRw NND_Carrier NNH_ModelCarrier NNH_Libraries

theorem value (base : Ops) (env : RSL.Env) (program pool : solana_pubkey.Pubkey)
 (p m c l r e v : r1_pool_adapter.owned.OwnedAccount) (lane : U8) (slot : U64) (out : RSL.Authenticated)
 (success : NNH_AuthTailValues.masterValue L D
  ⟨key program,[account p,account m,account c,account l,account r,account e,account v],key pool,byte lane,NND_Carrier.slot slot⟩
  (account p) (account m) (account c) (account l) (account r) (account e) (account v) env=.ok out) :
 ∃ master,
 NNH_AuthTailParts.master (NNH_Tx2ModelSlots.install base env) program m c l r e pool lane slot =
 NNH_AuthTailParts.checkpoint (NNH_Tx2ModelSlots.install base env) program m c l r e pool lane slot m.key master ∧
 NNH_AuthTailValues.checkpointValue L D
  ⟨key program,[account p,account m,account c,account l,account r,account e,account v],key pool,byte lane,NND_Carrier.slot slot⟩
  (account p) (account m) (account c) (account l) (account r) (account e) (account v) env (NND_Carrier.master master)=.ok out := by
 obtain ⟨packet⟩ := NNH_AuthMasterInputs.produce base env program pool p m c l r e v lane slot out success
 have registry := NNH_Tx2RegistryPort.value base env program pool m packet.master r e slot
 rw [packet.registry] at registry
 refine ⟨packet.master,?_,packet.next⟩
 apply NNH_AuthMasterStep.source base env program pool m c l r e lane slot packet.data packet.master
  packet.read packet.decode packet.pool_eq packet.mask_eq packet.pda
 exact registry
#print axioms value
end NNH_AuthMasterPort
