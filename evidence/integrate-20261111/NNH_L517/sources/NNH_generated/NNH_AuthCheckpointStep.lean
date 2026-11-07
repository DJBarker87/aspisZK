import NNH_AuthMasterStep
set_option autoImplicit false
noncomputable section
namespace NNH_AuthCheckpointStep
open Aeneas Aeneas.Std Result AdapterRw
attribute [local instance] Classical.propDecidable

theorem source (base : Ops) (env : RSL.Env)
 (program pool : solana_pubkey.Pubkey)
 (m c l r e : r1_pool_adapter.owned.OwnedAccount) (lane : U8) (slot : U64)
 (master : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1)
 (data : Slice U8) (ck : aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestCheckpointV1)
 (read : r1_pool_adapter.owned.OwnedAccount.data (NNH_Tx2ModelSlots.install base env) c=.ok (.Ok data))
 (decode : NKF_CheckpointBox.reference data=.ok (.Ok ck))
 (pool_eq : ck.master=m.key) (domain_eq : ck.deployment_domain=master.identity.deployment_domain)
 (pda : (NNH_Tx2ModelSlots.install base env).op38 (NNH_AuthSeeds.checkpoint m.key ck.checkpoint_sequence ck.bump) pool=.ok (.Ok c.key)) :
 NNH_AuthTailParts.checkpoint (NNH_Tx2ModelSlots.install base env) program m c l r e pool lane slot m.key master =
 NNH_AuthTailParts.lane (NNH_Tx2ModelSlots.install base env) program m c l r e pool lane slot m.key master ck c.key := by
 have decoder : (NNH_Tx2ModelSlots.install base env).op49 data=.ok (.Ok ck) := decode
 unfold NNH_AuthTailParts.checkpoint
 simp only [read,bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch,decoder,
  NNH_AuthSlotFacts.bytes,NGL_ArrayEquality.ne_value,pool_eq,domain_eq,
  decide_true,Bool.not_true,Bool.false_eq_true,if_false,NNH_AuthSlotFacts.asRef,lift]
 unfold NNH_AuthSeeds.checkpoint NNH_MPdaSeeds.one at pda
 rw [pda]
 simp only [bind_tc_ok,core.result.Result.map_err,AspisR1.Port4C_GeometryStd.mapError,
  core.result.Result.Insts.CoreOpsTry.branch,r1_pool_adapter.owned.OwnedAccount.impl.key,
  NNH_AuthSlotFacts.ne_self,Bool.false_eq_true,if_false]
#print axioms source
end NNH_AuthCheckpointStep
