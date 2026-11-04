import Lean
import NFY_Part045
import NFY_Part046

-- BEGIN copied JHd_RequestPayload: lean/JHd_RequestPayload.lean
set_option autoImplicit false
namespace AspisR1.NFY_JHd_RequestPayload
open Aeneas Aeneas.Std Result
open AspisR20Request pool_v1.payment_relation

theorem source : decode_pool_v1_private_transfer_public_v1 NFY_JFu_PublicRange.payment=
    ok (.Ok NFY_JHd_RequestPayment.value) := by
  have validated:=NFY_JHd_RequestPayment.validated
  unfold NFY_JHd_RequestPayment.value at validated
  unfold decode_pool_v1_private_transfer_public_v1
  simp only [NFY_JFs_PaymentArray.shared,NFY_JHd_RequestHeader.source,bind_tc_ok,
    AspisR20Request.core.result.Result.map_err,core.result.Result.Insts.CoreOpsTry.branch,
    AMOUNT_OR_RESERVED_OFFSET,FIRST_OUTPUT_OR_DESTINATION_OFFSET,SECOND_OUTPUT_OFFSET]
  simp only [NFY_JFs_PaymentArray.range 148#usize 152#usize (by decide) (by decide),
    show (148#usize).val=148 from rfl,show (152#usize).val=152 from rfl,
    Nat.reduceAdd,Nat.reduceSub,NFY_JFs_PaymentReads.fee_selected,
    POOL_V1_CANONICAL_FEE,NFY_JFs_PaymentReads.fee_bytes,lift,bind_tc_ok]
  have fee_slice : core.array.Array.index
      (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice U8))
      (⟨NFY_JFu_PublicMeta08.bytes,by simp [NFY_JFu_PublicMeta08.bytes]⟩ : Array U8 4#usize)
      {start:=0#usize,«end»:=4#usize}=ok NFY_JFs_PaymentReads.fee := by rfl
  simp only [fee_slice,NFY_JFs_PaymentReads.fee_compare,bind_tc_ok,Bool.false_eq_true,↓reduceIte,
    NFY_JHd_RequestCommon.source,core.result.Result.Insts.CoreOpsTry.branch]
  simp only [NFY_JFs_PaymentArray.range 152#usize 184#usize (by decide) (by decide),
    NFY_JFs_PaymentArray.suffix 184#usize (by decide),
    show (152#usize).val=152 from rfl,show (184#usize).val=184 from rfl,
    Nat.reduceAdd,Nat.reduceSub,NFY_JFs_PaymentDigests.shared45,NFY_JFs_PaymentDigests.shared46,
    atomic_statement.unwrap_fixed_slice,NFY_JHd_RequestDigests.decode45,NFY_JHd_RequestDigests.decode46,
    bind_tc_ok,AspisR20Request.core.result.Result.map_err,core.result.Result.Insts.CoreOpsTry.branch,validated]
  rfl

#print axioms source
end AspisR1.NFY_JHd_RequestPayload
-- END copied JHd_RequestPayload

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
