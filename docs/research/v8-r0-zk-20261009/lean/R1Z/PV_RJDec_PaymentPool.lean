import AspisR1TerminalDecoder.Funs
set_option autoImplicit false
namespace R1Z.PV_RJDec_PaymentPool
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder
open pool_v1.payment_relation

theorem rejection (s : CommonPublicV1)
    (bad : core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8 s.pool (Array.repeat 32#usize 0#u8) = ok true) :
    validate_common s = ok (.Err PoolV1PaymentStatementFormatError.ZeroRequiredBinding) := by
  unfold validate_common
  simp only [bad, bind_tc_ok, Bool.false_eq_true, Bool.true_eq_true, ↓reduceIte]

#print axioms rejection
end R1Z.PV_RJDec_PaymentPool
