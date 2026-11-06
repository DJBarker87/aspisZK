import PCA_Packet
set_option autoImplicit false
namespace PCA
/-- OPEN schema for programs/aspis-pool/src/processor.rs::plan_fresh_program_pda. Class D.
Not a root: native and reference have not been fixed to CLOSED certificates.
The state includes the full admitted list and every touched/untouched cell.
Complete concrete Result/domain/frames remain a child obligation. -/
abbrev Args_POOL_362 := Nat × Key × Key × Nat
abbrev Reply_POOL_362 := Preparation
def RowSpec_POOL_362
    (native reference : Args_POOL_362 → PCA_State → Execution Reply_POOL_362) : Prop :=
  FullPacket native reference
end PCA
