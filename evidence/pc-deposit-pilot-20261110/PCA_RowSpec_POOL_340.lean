import PCA_Packet
set_option autoImplicit false
namespace PCA
/-- OPEN schema for programs/aspis-pool/src/pair_forest.rs::validate_lane_current_page. Class D.
Not a root: native and reference have not been fixed to CLOSED certificates.
The state includes the full admitted list and every touched/untouched cell.
Complete concrete Result/domain/frames remain a child obligation. -/
abbrev Args_POOL_340 := Key × Nat × Nat × Lane × Bool × Option UInt8
abbrev Reply_POOL_340 := Header
def RowSpec_POOL_340
    (native reference : Args_POOL_340 → PCA_State → Execution Reply_POOL_340) : Prop :=
  FullPacket native reference
end PCA
