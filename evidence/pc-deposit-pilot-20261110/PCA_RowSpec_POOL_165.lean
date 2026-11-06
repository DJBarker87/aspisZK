import PCA_Packet
set_option autoImplicit false
namespace PCA
/-- OPEN schema for crates/aspis-statement/src/pool_v1/format.rs::pool_v1_note_commitment. Class A.
Not a root: native and reference have not been fixed to CLOSED certificates.
The state includes the full admitted list and every touched/untouched cell.
Complete concrete Result/domain/frames remain a child obligation. -/
abbrev Args_POOL_165 := Digest × UInt32 × UInt32 × Digest
abbrev Reply_POOL_165 := Digest
def RowSpec_POOL_165
    (native reference : Args_POOL_165 → PCA_State → Execution Reply_POOL_165) : Prop :=
  FullPacket native reference
end PCA
