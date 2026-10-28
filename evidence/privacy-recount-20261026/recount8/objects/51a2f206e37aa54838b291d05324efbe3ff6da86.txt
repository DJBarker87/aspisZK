import R1Z.PDict_FinalDictionary
set_option autoImplicit false
namespace R1Z.PDict_FinalTypes
open Aeneas Aeneas.Std ProverRwFull
abbrev native := PDict_FinalDictionary.native

theorem type1_installed (base : ExternalTypes) : (native base).op1 =
    PDict_PathTypes.std.fs.OpenOptions := rfl

theorem type2_installed (base : ExternalTypes) : (native base).op2 =
    PDict_PathTypes.std.path.Path := rfl

theorem type4_installed (base : ExternalTypes) : (native base).op4 =
    PDict_PathTypes.std.path.PathBuf := rfl

theorem type5_installed (base : ExternalTypes) : (native base).op5 =
    PDict_ReserveError.alloc.collections.TryReserveError := rfl

theorem type6_installed (base : ExternalTypes) : (native base).op6 =
    PDict_Carriers.aspis_core.state_only_prefix.r0.Error := rfl

theorem type7_installed (base : ExternalTypes) : (native base).op7 = PDict_ErrorCarrier.ErrorValue := rfl

theorem type8_installed (base : ExternalTypes) : (native base).op8 =
    PDict_Carriers.aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairHidingLayoutErrorV1 := rfl

theorem type9_installed (base : ExternalTypes) (U B : Type) : (native base).op9 U B =
    PDict_UInt.typenum.uint.UInt U B := rfl

theorem type10_installed (base : ExternalTypes) : (native base).op10 =
    PDict_CryptoTypes.sha2.core_api.Sha256VarCore := rfl

theorem type11_installed (base : ExternalTypes) : (native base).op11 =
    PDict_CryptoTypes.generic_array.GenericArray := rfl

theorem type12_installed (base : ExternalTypes) : (native base).op12 =
    PDict_CryptoTypes.generic_array.GenericArrayImplOdd := rfl

theorem type13_installed (base : ExternalTypes) : (native base).op13 =
    PDict_CryptoTypes.generic_array.GenericArrayImplEven := rfl

theorem type14_installed (base : ExternalTypes) : (native base).op14 =
    PDict_CryptoTypes.block_buffer.BlockBuffer := rfl

theorem type15_installed (base : ExternalTypes) : (native base).op15 =
    PDict_CryptoTypes.digest.core_api.wrapper.CoreWrapper := rfl

theorem type16_installed (base : ExternalTypes) : (native base).op16 =
    PDict_CryptoTypes.digest.core_api.ct_variable.CtVariableCoreWrapper := rfl

theorem type17_installed (base : ExternalTypes) : (native base).op17 =
    PDict_StatementTypes.aspis_statement.pool_v1.pair_trace.PoolV1PairTraceErrorV1 := rfl

theorem type18_installed (base : ExternalTypes) : (native base).op18 =
    PDict_StatementTypes.aspis_statement.pool_v1.pair_trace.PoolV1PairTracePublicOutputsV1 := rfl

theorem type19_installed (base : ExternalTypes) : (native base).op19 =
    PDict_Carriers.aspis_statement.pool_v1.pair_trace.PoolV1PairTraceVariantV1 := rfl

theorem type20_installed (base : ExternalTypes) : (native base).op20 =
    PDict_StatementTypes.aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 := rfl

theorem type21_installed (base : ExternalTypes) : (native base).op21 =
    PDict_StatementTypes.aspis_statement.pool_v1.payment_relation.PoolV1WithdrawalPublicV1 := rfl

theorem type22_installed (base : ExternalTypes) : (native base).op22 =
    PDict_StatementTypes.aspis_statement.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1 := rfl

theorem type23_installed (base : ExternalTypes) : (native base).op23 =
    PDict_Carriers.aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairCopyRowLinkKindV1 := rfl

theorem type24_installed (base : ExternalTypes) : (native base).op24 =
    PDict_Carriers.aspis_statement.pool_v1.pair_trace.PoolV1PairCopyWeightV1 := rfl

theorem type25_installed (base : ExternalTypes) : (native base).op25 =
    PDict_Carriers.weights.Weights := rfl

theorem type26_installed (base : ExternalTypes) : (native base).op26 = U64 := rfl

#print axioms type1_installed
#print axioms type2_installed
#print axioms type4_installed
#print axioms type5_installed
#print axioms type6_installed
#print axioms type7_installed
#print axioms type8_installed
#print axioms type9_installed
#print axioms type10_installed
#print axioms type11_installed
#print axioms type12_installed
#print axioms type13_installed
#print axioms type14_installed
#print axioms type15_installed
#print axioms type16_installed
#print axioms type17_installed
#print axioms type18_installed
#print axioms type19_installed
#print axioms type20_installed
#print axioms type21_installed
#print axioms type22_installed
#print axioms type23_installed
#print axioms type24_installed
#print axioms type25_installed
#print axioms type26_installed
end R1Z.PDict_FinalTypes
