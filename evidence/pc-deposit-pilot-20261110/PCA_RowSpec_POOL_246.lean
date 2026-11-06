import PCA_Packet
set_option autoImplicit false
namespace PCA
/-- OPEN schema for crates/aspis-statement/src/pool_v1/root_history.rs::root_history_location. Class A.
Not a root: native and reference have not been fixed to CLOSED certificates.
The state includes the full admitted list and every touched/untouched cell.
Complete concrete Result/domain/frames remain a child obligation. -/
abbrev Args_POOL_246 := UInt64
abbrev Reply_POOL_246 := Location
def RowSpec_POOL_246
    (native reference : Args_POOL_246 → PCA_State → Execution Reply_POOL_246) : Prop :=
  FullPacket native reference
end PCA
