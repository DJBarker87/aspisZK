import PCA_Packet
set_option autoImplicit false
namespace PCA
/-- OPEN schema for programs/aspis-pool/src/pair_forest.rs::decode_terminal_master_box_v1. Class B.
Not a root: native and reference have not been fixed to CLOSED certificates.
The state includes the full admitted list and every touched/untouched cell.
Complete concrete Result/domain/frames remain a child obligation. -/
abbrev Args_POOL_313 := Key × Nat
abbrev Reply_POOL_313 := Master
def RowSpec_POOL_313
    (native reference : Args_POOL_313 → PCA_State → Execution Reply_POOL_313) : Prop :=
  FullPacket native reference
end PCA
