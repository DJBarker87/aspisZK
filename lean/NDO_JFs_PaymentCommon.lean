import NDO_JFs_PaymentValue
import NDO_JFs_PaymentReads
set_option autoImplicit false
namespace AspisR1.JFs_PaymentCommon
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder pool_v1.payment_relation

theorem source : decode_common JFs_PaymentArray.value=ok (.Ok JFs_PaymentValue.common) := by
  have validated:=JFs_PaymentValue.common_validated
  unfold JFs_PaymentValue.common at validated
  simp only [JFs_PaymentValue.asset] at validated
  have assetBound : ¬77#u32 >= aspis_core.field.P := by
    unfold aspis_core.field.P
    scalar_tac
  unfold decode_common
  simp only [ASSET_ID_OFFSET,AMOUNT_OR_RESERVED_OFFSET,POOL_OFFSET,DEPLOYMENT_DOMAIN_OFFSET,
    ANCHOR_SEQUENCE_OFFSET,ANCHOR_ROOT_OFFSET,NULLIFIER_OFFSET]
  simp only [
    JFs_PaymentArray.range 144#usize 148#usize (by decide) (by decide),
    JFs_PaymentArray.range 8#usize 40#usize (by decide) (by decide),
    JFs_PaymentArray.range 40#usize 72#usize (by decide) (by decide),
    JFs_PaymentArray.range 72#usize 80#usize (by decide) (by decide),
    JFs_PaymentArray.range 80#usize 112#usize (by decide) (by decide),
    JFs_PaymentArray.range 112#usize 144#usize (by decide) (by decide),
    show (8#usize).val=8 from rfl,
    show (40#usize).val=40 from rfl,
    show (72#usize).val=72 from rfl,
    show (80#usize).val=80 from rfl,
    show (112#usize).val=112 from rfl,
    show (144#usize).val=144 from rfl,
    show (148#usize).val=148 from rfl,
    Nat.reduceAdd,Nat.reduceSub,
    JFs_PaymentReads.cast4,JFs_PaymentReads.cast5,JFs_PaymentReads.cast6,JFs_PaymentReads.cast7,
    JFs_PaymentDigests.shared43,JFs_PaymentDigests.shared44,
    JFs_PaymentDigests.decode43,JFs_PaymentDigests.decode44,
    atomic_statement.unwrap_fixed_slice,lift,bind_tc_ok,
    JFs_PaymentValue.asset,assetBound,
    Bool.false_eq_true,↓reduceIte,
    core.result.Result.map_err,core.result.Result.Insts.CoreOpsTry.branch]
  simp only [validated,bind_tc_ok,
    core.result.Result.Insts.CoreOpsTry.branch]
  rfl

#print axioms source
end AspisR1.JFs_PaymentCommon
