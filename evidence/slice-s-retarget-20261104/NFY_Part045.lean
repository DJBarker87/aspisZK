import Lean
import NFY_Part044
import NFY_Part040

-- BEGIN copied JHd_RequestCommon: lean/JHd_RequestCommon.lean
set_option autoImplicit false
namespace AspisR1.NFY_JHd_RequestCommon
open Aeneas Aeneas.Std Result
open AspisR20Request pool_v1.payment_relation

theorem source : decode_common NFY_JFs_PaymentArray.value=ok (.Ok NFY_JHd_RequestPayment.common) := by
  have validated:=NFY_JHd_RequestPayment.common_validated
  unfold NFY_JHd_RequestPayment.common at validated
  simp only [NFY_JHd_RequestPayment.asset] at validated
  have assetBound : ¬77#u32 >= aspis_core.field.P := by
    unfold aspis_core.field.P
    scalar_tac
  unfold decode_common
  simp only [ASSET_ID_OFFSET,AMOUNT_OR_RESERVED_OFFSET,POOL_OFFSET,DEPLOYMENT_DOMAIN_OFFSET,
    ANCHOR_SEQUENCE_OFFSET,ANCHOR_ROOT_OFFSET,NULLIFIER_OFFSET]
  simp only [
    NFY_JFs_PaymentArray.range 144#usize 148#usize (by decide) (by decide),
    NFY_JFs_PaymentArray.range 8#usize 40#usize (by decide) (by decide),
    NFY_JFs_PaymentArray.range 40#usize 72#usize (by decide) (by decide),
    NFY_JFs_PaymentArray.range 72#usize 80#usize (by decide) (by decide),
    NFY_JFs_PaymentArray.range 80#usize 112#usize (by decide) (by decide),
    NFY_JFs_PaymentArray.range 112#usize 144#usize (by decide) (by decide),
    show (8#usize).val=8 from rfl,
    show (40#usize).val=40 from rfl,
    show (72#usize).val=72 from rfl,
    show (80#usize).val=80 from rfl,
    show (112#usize).val=112 from rfl,
    show (144#usize).val=144 from rfl,
    show (148#usize).val=148 from rfl,
    Nat.reduceAdd,Nat.reduceSub,
    NFY_JFs_PaymentReads.cast4,NFY_JFs_PaymentReads.cast5,NFY_JFs_PaymentReads.cast6,NFY_JFs_PaymentReads.cast7,
    NFY_JFs_PaymentDigests.shared43,NFY_JFs_PaymentDigests.shared44,
    NFY_JHd_RequestDigests.decode43,NFY_JHd_RequestDigests.decode44,
    atomic_statement.unwrap_fixed_slice,lift,bind_tc_ok,
    NFY_JHd_RequestPayment.asset,assetBound,
    Bool.false_eq_true,↓reduceIte,
    AspisR20Request.core.result.Result.map_err,core.result.Result.Insts.CoreOpsTry.branch]
  simp only [validated,bind_tc_ok,
    core.result.Result.Insts.CoreOpsTry.branch]
  rfl

#print axioms source
end AspisR1.NFY_JHd_RequestCommon
-- END copied JHd_RequestCommon

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
