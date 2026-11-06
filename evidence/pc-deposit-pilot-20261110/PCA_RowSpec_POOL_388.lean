import PCA_Packet
set_option autoImplicit false
namespace PCA
/-- OPEN schema for programs/aspis-pool/src/vault.rs::plan_legacy_deposit_transfer_from_identity_v1. Class D.
Not a root: native and reference have not been fixed to CLOSED certificates.
The state includes the full admitted list and every touched/untouched cell.
Complete concrete Result/domain/frames remain a child obligation. -/
abbrev Args_POOL_388 := Key × Bytes × Identity × List Nat × UInt32
abbrev Reply_POOL_388 := TransferPlan
def RowSpec_POOL_388
    (native reference : Args_POOL_388 → PCA_State → Execution Reply_POOL_388) : Prop :=
  FullPacket native reference
end PCA
