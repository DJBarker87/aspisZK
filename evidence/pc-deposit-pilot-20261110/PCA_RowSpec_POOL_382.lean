import PCA_Packet
set_option autoImplicit false
namespace PCA
/-- OPEN schema for programs/aspis-pool/src/vault.rs::exact_transfer_account_infos_v1. Class D.
Not a root: native and reference have not been fixed to CLOSED certificates.
The state includes the full admitted list and every touched/untouched cell.
Complete concrete Result/domain/frames remain a child obligation. -/
abbrev Args_POOL_382 := List Nat
abbrev Reply_POOL_382 := Vector Nat 5
def RowSpec_POOL_382
    (native reference : Args_POOL_382 → PCA_State → Execution Reply_POOL_382) : Prop :=
  FullPacket native reference
end PCA
