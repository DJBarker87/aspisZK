import R1Z.PDict_CarrierInstall
import R1Z.PDict_StatementTypesSource
import R1Z.PDict_CryptoTypesSource
import R1Z.PDict_UIntOps
set_option autoImplicit false
namespace R1Z.PDict_MoreCarriers
open Aeneas Aeneas.Std ProverRwFull

/-- Twelve further transparent source carriers. F64 is its complete64-bit
encoding, checked by the native P6 codec contract, including NaN payloads.
No floating arithmetic interpretation or IO wrapper law is added. -/
@[reducible] def native (base : ExternalTypes) : ExternalTypes :=
  { PDict_CarrierInstall.native base with
    op10 := PDict_CryptoTypes.sha2.core_api.Sha256VarCore
    op11 := PDict_CryptoTypes.generic_array.GenericArray
    op12 := PDict_CryptoTypes.generic_array.GenericArrayImplOdd
    op13 := PDict_CryptoTypes.generic_array.GenericArrayImplEven
    op14 := PDict_CryptoTypes.block_buffer.BlockBuffer
    op15 := PDict_CryptoTypes.digest.core_api.wrapper.CoreWrapper
    op16 := PDict_CryptoTypes.digest.core_api.ct_variable.CtVariableCoreWrapper
    op17 := PDict_StatementTypes.aspis_statement.pool_v1.pair_trace.PoolV1PairTraceErrorV1
    op18 := PDict_StatementTypes.aspis_statement.pool_v1.pair_trace.PoolV1PairTracePublicOutputsV1
    op20 := PDict_StatementTypes.aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1
    op21 := PDict_StatementTypes.aspis_statement.pool_v1.payment_relation.PoolV1WithdrawalPublicV1
    op22 := PDict_StatementTypes.aspis_statement.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1
    op26 := U64 }

theorem type10 (base : ExternalTypes) : (native base).op10 =
    PDict_CryptoTypes.sha2.core_api.Sha256VarCore := rfl

theorem type11 (base : ExternalTypes) : (native base).op11 =
    PDict_CryptoTypes.generic_array.GenericArray := rfl

theorem type12 (base : ExternalTypes) : (native base).op12 =
    PDict_CryptoTypes.generic_array.GenericArrayImplOdd := rfl

theorem type13 (base : ExternalTypes) : (native base).op13 =
    PDict_CryptoTypes.generic_array.GenericArrayImplEven := rfl

theorem type14 (base : ExternalTypes) : (native base).op14 =
    PDict_CryptoTypes.block_buffer.BlockBuffer := rfl

theorem type15 (base : ExternalTypes) : (native base).op15 =
    PDict_CryptoTypes.digest.core_api.wrapper.CoreWrapper := rfl

theorem type16 (base : ExternalTypes) : (native base).op16 =
    PDict_CryptoTypes.digest.core_api.ct_variable.CtVariableCoreWrapper := rfl

theorem type17 (base : ExternalTypes) : (native base).op17 =
    PDict_StatementTypes.aspis_statement.pool_v1.pair_trace.PoolV1PairTraceErrorV1 := rfl

theorem type18 (base : ExternalTypes) : (native base).op18 =
    PDict_StatementTypes.aspis_statement.pool_v1.pair_trace.PoolV1PairTracePublicOutputsV1 := rfl

theorem type20 (base : ExternalTypes) : (native base).op20 =
    PDict_StatementTypes.aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 := rfl

theorem type21 (base : ExternalTypes) : (native base).op21 =
    PDict_StatementTypes.aspis_statement.pool_v1.payment_relation.PoolV1WithdrawalPublicV1 := rfl

theorem type22 (base : ExternalTypes) : (native base).op22 =
    PDict_StatementTypes.aspis_statement.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1 := rfl

theorem type26 (base : ExternalTypes) : (native base).op26 = U64 := rfl

theorem carrier_retraction (base : ExternalTypes) :
    PDict_CarrierInstall.native (native base) = native base := rfl

/-- The previously installed source entries and six UInt field operations at
this same partially concrete native type dictionary. Eight IO carriers remain. -/
@[reducible] noncomputable def selected (base : ExternalTypes)
    (ops : @ExternalFuns (native base)) : @ExternalFuns (native base) :=
  @PDict_UIntOps.selected (native base) ops

#print axioms type10
#print axioms type11
#print axioms type12
#print axioms type13
#print axioms type14
#print axioms type15
#print axioms type16
#print axioms type17
#print axioms type18
#print axioms type20
#print axioms type21
#print axioms type22
#print axioms type26
#print axioms carrier_retraction
end R1Z.PDict_MoreCarriers
