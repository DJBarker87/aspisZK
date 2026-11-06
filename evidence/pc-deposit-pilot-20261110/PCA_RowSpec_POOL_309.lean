import PCA_Packet
set_option autoImplicit false
namespace PCA
/-- OPEN schema for programs/aspis-pool/src/pair_forest.rs::decode_pair_forest_deposit_instruction_v1. Class B.
Not a root: native and reference have not been fixed to CLOSED certificates.
The state includes the full admitted list and every touched/untouched cell.
Complete concrete Result/domain/frames remain a child obligation. -/
abbrev Args_POOL_309 := Bytes
abbrev Reply_POOL_309 := Request
def RowSpec_POOL_309
    (native reference : Args_POOL_309 → PCA_State → Execution Reply_POOL_309) : Prop :=
  FullPacket native reference
end PCA
