import PCA_Packet
set_option autoImplicit false
namespace PCA
/-- OPEN schema for programs/aspis-pool/src/history.rs::append_roots_unchecked. Class A.
Not a root: native and reference have not been fixed to CLOSED certificates.
The state includes the full admitted list and every touched/untouched cell.
Complete concrete Result/domain/frames remain a child obligation. -/
abbrev Args_POOL_279 := NLF_RefCell.Guard × Header × List Digest
abbrev Reply_POOL_279 := Unit
def RowSpec_POOL_279
    (native reference : Args_POOL_279 → PCA_State → Execution Reply_POOL_279) : Prop :=
  FullPacket native reference
end PCA
