import NNH_AuthCheckpointStep
import NNH_AuthResult
set_option autoImplicit false
noncomputable section
namespace NNH_AuthLaneStep
open Aeneas Aeneas.Std Result AdapterRw
attribute [local instance] Classical.propDecidable

theorem source (base : Ops) (env : RSL.Env)
 (program pool : solana_pubkey.Pubkey)
 (m c l r e : r1_pool_adapter.owned.OwnedAccount) (lane : U8) (slot : U64)
 (master : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
 (ck : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestCheckpointV1)
 (data : Slice U8) (state : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestLaneStateV1)
 (read : r1_pool_adapter.owned.OwnedAccount.data (NNH_Tx2ModelSlots.install base env) l=.ok (.Ok data))
 (decode : NNH_LaneModel.decode data=.ok (.Ok state))
 (pool_eq : state.master=m.key) (lane_eq : state.lane_id=lane)
 (pda : (NNH_Tx2ModelSlots.install base env).op38 (NNH_AuthSeeds.lane m.key lane state.bump) pool=.ok (.Ok l.key)) :
 NNH_AuthTailParts.lane (NNH_Tx2ModelSlots.install base env) program m c l r e pool lane slot m.key master ck c.key =
 .ok (.Ok (NNH_AuthResult.value master ck state m.key c.key l.key)) := by
 have decoder : (NNH_Tx2ModelSlots.install base env).op50 data=.ok (.Ok state) := decode
 unfold NNH_AuthTailParts.lane
 simp only [read,bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch,decoder,
  NNH_AuthSlotFacts.bytes,NGL_ArrayEquality.ne_value,pool_eq,lane_eq,bne_self_eq_false,
  decide_true,Bool.not_true,Bool.false_eq_true,if_false,NNH_AuthSlotFacts.asRef,lift]
 unfold NNH_AuthSeeds.lane NNH_MPdaSeeds.one at pda
 rw [pda]
 simp only [bind_tc_ok,core.result.Result.map_err,AspisR1.Port4C_GeometryStd.mapError,
  core.result.Result.Insts.CoreOpsTry.branch,r1_pool_adapter.owned.OwnedAccount.impl.key,
  NNH_AuthSlotFacts.ne_self,Bool.false_eq_true,if_false,NNH_AuthSlotFacts.bytes]
 rfl
#print axioms source
end NNH_AuthLaneStep
