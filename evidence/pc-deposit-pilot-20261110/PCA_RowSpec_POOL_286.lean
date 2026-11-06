import PCA_Packet
set_option autoImplicit false
namespace PCA
/-- OPEN schema for programs/aspis-pool/src/history.rs::write_new_page_unchecked. Class B.
Not a root: native and reference have not been fixed to CLOSED certificates.
The state includes the full admitted list and every touched/untouched cell.
Complete concrete Result/domain/frames remain a child obligation. -/
abbrev Args_POOL_286 := NLF_RefCell.Guard × Bytes × UInt64 × UInt64 × List Digest
abbrev Reply_POOL_286 := Unit
def RowSpec_POOL_286
    (native reference : Args_POOL_286 → PCA_State → Execution Reply_POOL_286) : Prop :=
  FullPacket native reference
end PCA
