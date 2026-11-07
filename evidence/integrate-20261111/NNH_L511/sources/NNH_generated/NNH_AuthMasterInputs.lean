import NNH_AuthMasterCut
import NNH_BoxOk
import NNH_MappedOk
import NNH_AuthGuardPorts
import NNH_AuthSeeds
import NNH_PdaOk
set_option autoImplicit false
noncomputable section
namespace NNH_AuthMasterInputs
open Aeneas Aeneas.Std AdapterRw NND_Carrier NNH_ModelCarrier NNH_Libraries
attribute [local instance] Classical.propDecidable

structure Packet (base : Ops) (env : RSL.Env) (program pool : solana_pubkey.Pubkey)
 (p m c l r e v : r1_pool_adapter.owned.OwnedAccount) (lane : U8) (slot : U64) (out : RSL.Authenticated) where
 data : Slice U8
 read : r1_pool_adapter.owned.OwnedAccount.data (NNH_Tx2ModelSlots.install base env) m=.ok (.Ok data)
 master : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1
 decode : NKF_MasterBox.reference data=.ok (.Ok master)
 pool_eq : master.identity.pool=m.key
 mask_eq : master.initialized_lane_mask=255#u8
 pda : (NNH_Tx2ModelSlots.install base env).op38 (NNH_AuthSeeds.master master.identity.asset_mint master.bump) pool=.ok (.Ok m.key)
 registry : NNH_RegistryEval.value L D (NNH_MRegistryArgs.args program pool m master r e slot) env=.ok ()
 next : NNH_AuthTailValues.checkpointValue L D
  ⟨key program,[account p,account m,account c,account l,account r,account e,account v],key pool,byte lane,NND_Carrier.slot slot⟩
  (account p) (account m) (account c) (account l) (account r) (account e) (account v) env (NND_Carrier.master master)=.ok out

theorem produce (base : Ops) (env : RSL.Env) (program pool : solana_pubkey.Pubkey)
 (p m c l r e v : r1_pool_adapter.owned.OwnedAccount) (lane : U8) (slot : U64) (out : RSL.Authenticated)
 (success : NNH_AuthTailValues.masterValue L D
  ⟨key program,[account p,account m,account c,account l,account r,account e,account v],key pool,byte lane,NND_Carrier.slot slot⟩
  (account p) (account m) (account c) (account l) (account r) (account e) (account v) env=.ok out) :
 Nonempty (Packet base env program pool p m c l r e v lane slot out) := by
 obtain ⟨cut⟩ := NNH_AuthMasterCut.produce _ _ _ _ _ _ _ _ _ _ _ _ success
 rcases cut with ⟨bytes,data_ok,master,decode_ok,guard_ok,pda_ok,registry_ok,next_ok⟩
 have read := NNH_AuthGuardPorts.data base env m
 rw [data_ok] at read
 obtain ⟨data,read,data_eq⟩ := NNH_MappedOk.value _ _ _ read
 rw [←data_eq] at decode_ok
 obtain ⟨native,decode,native_eq⟩ := NNH_BoxOk.master data master decode_ok
 subst master
 have guard : native.identity.pool=m.key ∧ native.initialized_lane_mask=255#u8 := by
  simp only [Bool.or_eq_false_iff,decide_eq_false_iff_not,not_not,bne_eq_false_iff_eq] at guard_ok
  constructor
  · exact (key_eq_iff _ _).mp guard_ok.1
  · exact (byte_eq_iff _ _).mp guard_ok.2
 have pda : (NNH_Tx2ModelSlots.install base env).op38 (NNH_AuthSeeds.master native.identity.asset_mint native.bump) pool=.ok (.Ok m.key) := by
  apply NNH_PdaOk.native
  rw [NNH_AuthSeeds.master_bytes]
  exact pda_ok
 exact ⟨⟨data,read,native,decode,guard.1,guard.2,pda,registry_ok,next_ok⟩⟩
#print axioms produce
end NNH_AuthMasterInputs
