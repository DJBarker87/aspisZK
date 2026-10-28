import AdapterRwScalar
import NDO_JHd_RequestBindings
import NDO_JHd_RequestHead
import NDO_JHd_RequestSuffix
set_option autoImplicit false
namespace AspisR1.JHd_RequestDecode
open Aeneas Aeneas.Std Result
open AspisR20Request pool_v1.pair_forest_terminal
attribute [local irreducible] JHd_RequestWindow.value JHd_RequestValue.value

theorem source : decode_pool_v1_pair_forest_terminal_request_reference_v1
    JHd_RequestWindow.value=ok (.Ok JHd_RequestValue.value) := by
  have size : Slice.len JHd_RequestWindow.value.to_slice=320#usize := by
    have h : JHd_RequestWindow.value.to_slice.val.length=320 := by
      simp only [JHd_RequestWindow.value,Array.to_slice]
      exact JHb_DataRequest.length
    scalar_tac
  have reqSize : POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_BYTES=ok 320#usize := by
    unfold POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_BYTES pool_v1.payment_relation.POOL_V1_PAYMENT_STATEMENT_BYTES
    rw [AdapterRw.Scalar.mul_eq 3#usize 32#usize 96#usize (by scalar_tac),bind_tc_ok,
      AdapterRw.Scalar.add_eq 8#usize 96#usize 104#usize (by scalar_tac),bind_tc_ok]
    exact AdapterRw.Scalar.add_eq _ _ _ (by scalar_tac)
  have magic : Slice.Insts.CoreCmpPartialEqArray.ne core.cmp.PartialEqU8
      JHd_RequestHead.magic POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_MAGIC=ok false := by
    unfold POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_MAGIC JHd_RequestHead.magic
    rfl
  have kind : transition_kind 1#u8=ok (.Ok pool_v1.historical_anchor.PoolV1TransitionKind.PrivateTransfer) := by
    unfold transition_kind
    rfl
  unfold decode_pool_v1_pair_forest_terminal_request_reference_v1
  simp only [lift,reqSize,bind_tc_ok,size,
    show (320#usize !=320#usize)=false from rfl,Bool.false_eq_true,↓reduceIte,
    JHd_RequestHead.first,magic,JHd_RequestHead.b4,JHd_RequestHead.b5,
    JHd_RequestHead.b6,JHd_RequestHead.b7,
    POOL_V1_PAIR_FOREST_TERMINAL_VERSION,pool_v1.format.POOL_V1_DIGEST_ENCODING_VERSION,
    show (1#u8 !=1#u8)=false from rfl,show (0#u8 !=0#u8)=false from rfl,
    kind,core.result.Result.Insts.CoreOpsTry.branch,REQUEST_PAYMENT_OFFSET,
    JHd_RequestSuffix.source,JHd_RequestPayload.source,core.result.Result.map_err]
  simp only [REQUEST_PROFILE_OFFSET,REQUEST_RELEASE_OFFSET,REQUEST_POOL_PROGRAM_OFFSET,
    JHd_RequestBindings.profile,JHd_RequestBindings.release,JHd_RequestBindings.pool,
    JHd_RequestBindings.profile_cast,JHd_RequestBindings.release_cast,JHd_RequestBindings.pool_cast,
    bind_tc_ok,core.result.Result.map_err,core.result.Result.Insts.CoreOpsTry.branch,
    JHd_RequestValue.profile_nonzero,JHd_RequestValue.release_nonzero,JHd_RequestValue.pool_nonzero,
    Bool.false_eq_true,↓reduceIte]
  unfold JHd_RequestValue.value
  rfl
#print axioms source
end AspisR1.JHd_RequestDecode
