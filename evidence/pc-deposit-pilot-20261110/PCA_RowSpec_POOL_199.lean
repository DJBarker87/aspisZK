import PCA_Packet
set_option autoImplicit false
namespace PCA
/-- OPEN schema for crates/aspis-statement/src/pool_v1/pair_forest_accounts.rs::pool_v1_pair_forest_deposit_lane_v1. Class B.
Not a root: native and reference have not been fixed to CLOSED certificates.
The state includes the full admitted list and every touched/untouched cell.
Complete concrete Result/domain/frames remain a child obligation. -/
abbrev Args_POOL_199 := Digest
abbrev Reply_POOL_199 := UInt8
def RowSpec_POOL_199
    (native reference : Args_POOL_199 → PCA_State → Execution Reply_POOL_199) : Prop :=
  FullPacket native reference
end PCA
