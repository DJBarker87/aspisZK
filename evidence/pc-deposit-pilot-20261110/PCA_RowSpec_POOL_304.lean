import PCA_Packet
set_option autoImplicit false
namespace PCA
/-- OPEN schema for programs/aspis-pool/src/pair_forest.rs::decode_deposit_lane_box_v1. Class B.
Not a root: native and reference have not been fixed to CLOSED certificates.
The state includes the full admitted list and every touched/untouched cell.
Complete concrete Result/domain/frames remain a child obligation. -/
abbrev Args_POOL_304 := Key × Bytes × UInt8 × Nat
abbrev Reply_POOL_304 := Lane
def RowSpec_POOL_304
    (native reference : Args_POOL_304 → PCA_State → Execution Reply_POOL_304) : Prop :=
  FullPacket native reference
end PCA
