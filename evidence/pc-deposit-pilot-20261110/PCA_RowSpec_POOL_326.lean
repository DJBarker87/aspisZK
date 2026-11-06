import PCA_Packet
set_option autoImplicit false
namespace PCA
/-- OPEN schema for programs/aspis-pool/src/pair_forest.rs::prepare_deposit_append_v1. Class B.
Not a root: native and reference have not been fixed to CLOSED certificates.
The state includes the full admitted list and every touched/untouched cell.
Complete concrete Result/domain/frames remain a child obligation. -/
abbrev Args_POOL_326 := Lane × UInt8 × Digest
abbrev Reply_POOL_326 := Append × Vector UInt8 768
def RowSpec_POOL_326
    (native reference : Args_POOL_326 → PCA_State → Execution Reply_POOL_326) : Prop :=
  FullPacket native reference
end PCA
