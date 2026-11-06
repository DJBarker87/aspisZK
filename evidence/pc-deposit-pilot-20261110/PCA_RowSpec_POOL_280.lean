import PCA_Packet
set_option autoImplicit false
namespace PCA
/-- OPEN schema for programs/aspis-pool/src/history.rs::pool_v1_root_page_address. Class A.
Not a root: native and reference have not been fixed to CLOSED certificates.
The state includes the full admitted list and every touched/untouched cell.
Complete concrete Result/domain/frames remain a child obligation. -/
abbrev Args_POOL_280 := Key × Bytes × UInt64
abbrev Reply_POOL_280 := Key × UInt8
def RowSpec_POOL_280
    (native reference : Args_POOL_280 → PCA_State → Execution Reply_POOL_280) : Prop :=
  FullPacket native reference
end PCA
