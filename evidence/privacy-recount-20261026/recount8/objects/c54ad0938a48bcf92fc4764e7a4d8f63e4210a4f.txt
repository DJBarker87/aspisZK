import R1Z.PDict_UIntSource
import R1Z.PDict_CarriersSource
import R1Z.ProverRwFullExternalTypes
set_option autoImplicit false
namespace R1Z.PDict_CarrierInstall
open ProverRwFull

/-- Native source carriers from transparent, type-only Charon/Aeneas output.
The other21 fields remain explicit. No opaque child representation is hidden. -/
def native (base : ExternalTypes) : ExternalTypes :=
  { base with
    op6 := PDict_Carriers.aspis_core.state_only_prefix.r0.Error
    op8 := PDict_Carriers.aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairHidingLayoutErrorV1
    op9 := PDict_UInt.typenum.uint.UInt
    op19 := PDict_Carriers.aspis_statement.pool_v1.pair_trace.PoolV1PairTraceVariantV1
    op23 := PDict_Carriers.aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairCopyRowLinkKindV1
    op24 := PDict_Carriers.aspis_statement.pool_v1.pair_trace.PoolV1PairCopyWeightV1
    op25 := PDict_Carriers.weights.Weights }

theorem type6 (base : ExternalTypes) : (native base).op6 =
    PDict_Carriers.aspis_core.state_only_prefix.r0.Error := rfl

theorem type8 (base : ExternalTypes) : (native base).op8 =
    PDict_Carriers.aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairHidingLayoutErrorV1 := rfl

theorem type9 (base : ExternalTypes) (U B : Type) : (native base).op9 U B =
    PDict_UInt.typenum.uint.UInt U B := rfl

theorem type19 (base : ExternalTypes) : (native base).op19 =
    PDict_Carriers.aspis_statement.pool_v1.pair_trace.PoolV1PairTraceVariantV1 := rfl

theorem type23 (base : ExternalTypes) : (native base).op23 =
    PDict_Carriers.aspis_statement.pool_v1.pair_tree_hiding.PoolV1PairCopyRowLinkKindV1 := rfl

theorem type24 (base : ExternalTypes) : (native base).op24 =
    PDict_Carriers.aspis_statement.pool_v1.pair_trace.PoolV1PairCopyWeightV1 := rfl

theorem type25 (base : ExternalTypes) : (native base).op25 =
    PDict_Carriers.weights.Weights := rfl

#print axioms type6
#print axioms type8
#print axioms type9
#print axioms type19
#print axioms type23
#print axioms type24
#print axioms type25
end R1Z.PDict_CarrierInstall
