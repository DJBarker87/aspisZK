import NDO_JHd_RequestCommon
import NDO_JHd_RequestHeader
set_option autoImplicit false
namespace AspisR1.JHd_RequestPayload
open Aeneas Aeneas.Std Result
open AspisR20Request pool_v1.payment_relation

theorem source : decode_pool_v1_private_transfer_public_v1 JFu_PublicRange.payment=
    ok (.Ok JHd_RequestPayment.value) := by
  have validated:=JHd_RequestPayment.validated
  unfold JHd_RequestPayment.value at validated
  unfold decode_pool_v1_private_transfer_public_v1
  simp only [JFs_PaymentArray.shared,JHd_RequestHeader.source,bind_tc_ok,
    core.result.Result.map_err,core.result.Result.Insts.CoreOpsTry.branch,
    AMOUNT_OR_RESERVED_OFFSET,FIRST_OUTPUT_OR_DESTINATION_OFFSET,SECOND_OUTPUT_OFFSET]
  simp only [JFs_PaymentArray.range 148#usize 152#usize (by decide) (by decide),
    show (148#usize).val=148 from rfl,show (152#usize).val=152 from rfl,
    Nat.reduceAdd,Nat.reduceSub,JFs_PaymentReads.fee_selected,
    POOL_V1_CANONICAL_FEE,JFs_PaymentReads.fee_bytes,lift,bind_tc_ok]
  have fee_slice : core.array.Array.index
      (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice U8))
      (⟨JFu_PublicMeta08.bytes,by simp [JFu_PublicMeta08.bytes]⟩ : Array U8 4#usize)
      {start:=0#usize,«end»:=4#usize}=ok JFs_PaymentReads.fee := by rfl
  simp only [fee_slice,JFs_PaymentReads.fee_compare,bind_tc_ok,Bool.false_eq_true,↓reduceIte,
    JHd_RequestCommon.source,core.result.Result.Insts.CoreOpsTry.branch]
  simp only [JFs_PaymentArray.range 152#usize 184#usize (by decide) (by decide),
    JFs_PaymentArray.suffix 184#usize (by decide),
    show (152#usize).val=152 from rfl,show (184#usize).val=184 from rfl,
    Nat.reduceAdd,Nat.reduceSub,JFs_PaymentDigests.shared45,JFs_PaymentDigests.shared46,
    atomic_statement.unwrap_fixed_slice,JHd_RequestDigests.decode45,JHd_RequestDigests.decode46,
    bind_tc_ok,core.result.Result.map_err,core.result.Result.Insts.CoreOpsTry.branch,validated]
  rfl

#print axioms source
end AspisR1.JHd_RequestPayload
