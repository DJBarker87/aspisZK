import R1Z.PV_RJDec_ParserR17
import R1Z.PV_RJDec_ParserR10
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RJDec_PaymentPrefix
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder PV_W_TypedEffects
variable [ProverRwFull.ExternalTypes] [ProverRwFull.ExternalFuns]
theorem transfer_failure (bytes : Slice U8) (error : Aeneas.Std.Error)
    (first : core.array.TryFromSharedArraySlice.try_from 216#usize bytes = .fail error) :
    erase (inferInstance : ProverRwFull.ExternalFuns) (PV_RJDec_ParserR17.program bytes) = .fail error := by
  rw [PV_RJDec_ParserR17.source]
  simp only [pool_v1.payment_relation.decode_pool_v1_private_transfer_public_v1,first,bind_tc_fail]
#print axioms transfer_failure
theorem transfer_divergence (bytes : Slice U8)
    (first : core.array.TryFromSharedArraySlice.try_from 216#usize bytes = .div) :
    erase (inferInstance : ProverRwFull.ExternalFuns) (PV_RJDec_ParserR17.program bytes) = .div := by
  rw [PV_RJDec_ParserR17.source]
  simp only [pool_v1.payment_relation.decode_pool_v1_private_transfer_public_v1,first,bind_tc_div]
#print axioms transfer_divergence
theorem withdrawal_failure (bytes : Slice U8) (error : Aeneas.Std.Error)
    (first : core.array.TryFromSharedArraySlice.try_from 216#usize bytes = .fail error) :
    erase (inferInstance : ProverRwFull.ExternalFuns) (PV_RJDec_ParserR10.program bytes) = .fail error := by
  rw [PV_RJDec_ParserR10.source]
  simp only [pool_v1.payment_relation.decode_pool_v1_withdrawal_public_v1,first,bind_tc_fail]
#print axioms withdrawal_failure
theorem withdrawal_divergence (bytes : Slice U8)
    (first : core.array.TryFromSharedArraySlice.try_from 216#usize bytes = .div) :
    erase (inferInstance : ProverRwFull.ExternalFuns) (PV_RJDec_ParserR10.program bytes) = .div := by
  rw [PV_RJDec_ParserR10.source]
  simp only [pool_v1.payment_relation.decode_pool_v1_withdrawal_public_v1,first,bind_tc_div]
#print axioms withdrawal_divergence
end R1Z.PV_RJDec_PaymentPrefix
