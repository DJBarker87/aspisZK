import PCA_Packet
set_option autoImplicit false
namespace PCA
/-- OPEN schema for programs/aspis-pool/src/processor.rs::create_or_allocate_pda. Class B.
Not a root: native and reference have not been fixed to CLOSED certificates.
The state includes the full admitted list and every touched/untouched cell.
Complete concrete Result/domain/frames remain a child obligation. -/
abbrev Args_POOL_358 := Nat × Nat × Nat × Nat × Key × List Bytes
abbrev Reply_POOL_358 := Unit
def RowSpec_POOL_358
    (native reference : Args_POOL_358 → PCA_State → Execution Reply_POOL_358) : Prop :=
  FullPacket native reference
end PCA
