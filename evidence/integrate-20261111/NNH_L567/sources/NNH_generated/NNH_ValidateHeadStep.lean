import NNH_ValidateFission
import NNH_RequestOk
set_option autoImplicit false
noncomputable section
namespace NNH_ValidateHeadStep
open Aeneas Aeneas.Std Result AdapterRw NNH_Libraries
attribute [local instance] Classical.propDecidable

theorem source (base : Ops) (env : RSL.Env) (program : solana_pubkey.Pubkey)
 (xs : Slice r1_pool_adapter.owned.OwnedAccount) (data : Slice U8)
 (q : LIBB_PoolCarriers.Request) (lane : U8) (slot : U64)
 (length : data.val.length=320)
 (decode : AspisR1.NFY_JHd_RequestNative.decode data=.ok (.Ok q))
 (profile : q.verifier_profile=r1_pool_adapter.PROFILE_BINDING)
 (release : q.verifier_release=r1_pool_adapter.RELEASE_BINDING)
 (pool : q.pool_program=NND_Carrier.unkey D.pool)
 (lane_ok : NMS_RequestModels.outputLane (LIBB_PoolDecoders.nullifier q)=.ok (.Ok lane)) :
 NNH_ValidateFission.head (NNH_Tx2ModelSlots.install base env) program xs data (.Ok slot)=
 NNH_ValidateFission.authenticate (NNH_Tx2ModelSlots.install base env) program xs q q.pool_program lane slot := by
 have size : Slice.len data=320#usize := by
  apply UScalar.eq_of_val_eq
  exact length
 have constant : aspis_statement.pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_BYTES=.ok 320#usize := by
  unfold aspis_statement.pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_BYTES
   aspis_statement.pool_v1.payment_relation.POOL_V1_PAYMENT_STATEMENT_BYTES
  rfl
 have decoder : (NNH_Tx2ModelSlots.install base env).op23 data=.ok (.Ok q) := decode
 have deployed : (NNH_Tx2ModelSlots.install base env).op45=.ok (NND_Carrier.unkey D.pool) := rfl
 have nullifier : (NNH_Tx2ModelSlots.install base env).op20 q.«public»=.ok (LIBB_PoolDecoders.nullifier q) := NNH_RequestOk.nullifier q
 have outputLane : (NNH_Tx2ModelSlots.install base env).op17 (LIBB_PoolDecoders.nullifier q)=.ok (.Ok lane) := lane_ok
 unfold NNH_ValidateFission.head
 simp only [size,constant,bind_tc_ok,bne_self_eq_false,Bool.false_eq_true,if_false,decoder,
  core.result.Result.map_err,AspisR1.Port4C_GeometryStd.mapError,core.result.Result.Insts.CoreOpsTry.branch,
  NGL_ArrayEquality.ne_value,profile,release,pool,decide_true,Bool.not_true,deployed,
  NNH_AuthSlotFacts.fromBytes,nullifier,outputLane]
#print axioms source
end NNH_ValidateHeadStep
