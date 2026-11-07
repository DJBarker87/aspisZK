import NNH_AuthTailParts
import NNH_AuthSlotFacts
set_option autoImplicit false
noncomputable section
namespace NNH_AuthMasterStep
open Aeneas Aeneas.Std Result AdapterRw
attribute [local instance] Classical.propDecidable

theorem source (base : Ops) (env : RSL.Env)
 (program pool : solana_pubkey.Pubkey)
 (m c l r e : r1_pool_adapter.owned.OwnedAccount) (lane : U8) (slot : U64)
 (data : Slice U8) (master : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
 (read : r1_pool_adapter.owned.OwnedAccount.data (NNH_Tx2ModelSlots.install base env) m=.ok (.Ok data))
 (decode : NKF_MasterBox.reference data=.ok (.Ok master))
 (pool_eq : master.identity.pool=m.key) (mask_eq : master.initialized_lane_mask=255#u8)
 (pda : (NNH_Tx2ModelSlots.install base env).op38 (NNH_AuthSeeds.master master.identity.asset_mint master.bump) pool=.ok (.Ok m.key))
 (registry : r1_pool_adapter.owned.authenticate_invariant_release_registry (NNH_Tx2ModelSlots.install base env)
  program pool m master r e slot=.ok (.Ok ())) :
 NNH_AuthTailParts.master (NNH_Tx2ModelSlots.install base env) program m c l r e pool lane slot =
 NNH_AuthTailParts.checkpoint (NNH_Tx2ModelSlots.install base env) program m c l r e pool lane slot m.key master := by
 have decoder : (NNH_Tx2ModelSlots.install base env).op48 data=.ok (.Ok master) := decode
 unfold NNH_AuthTailParts.master
 simp only [read,bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch]
 simp only [decoder,bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch]
 simp only [r1_pool_adapter.owned.OwnedAccount.impl.key,bind_tc_ok,NNH_AuthSlotFacts.bytes,
  NGL_ArrayEquality.ne_value,pool_eq,decide_true,Bool.not_true,Bool.false_eq_true,if_false,
  NNH_AuthSlotFacts.mask,mask_eq,bne_self_eq_false,NNH_AuthSlotFacts.fromBytes,NNH_AuthSlotFacts.asRef,lift]
 unfold NNH_AuthSeeds.master NNH_MPdaSeeds.one at pda
 rw [pda]
 simp only [bind_tc_ok,core.result.Result.map_err,AspisR1.Port4C_GeometryStd.mapError,core.result.Result.Insts.CoreOpsTry.branch,
  NNH_AuthSlotFacts.ne_self,Bool.false_eq_true,if_false,registry]
#print axioms source
end NNH_AuthMasterStep
