import R1Z.PV_CB_Op84Funs
import R1Z.PV_CB_Merkle
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB_Op84Exact
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]
abbrev selected := PV_CB_Merkle.selected
theorem op84_source (ops : ExternalFuns)
    (hash : Slice (Slice U8) → Result (Array U8 32#usize)) (tag : U8) (values : Slice U8) :
    (selected ops).op84 hash tag values =
      PV_CB_ShippedOp84Fresh.aspis_core.r0.merkle.leaf hash tag values := rfl
#print axioms op84_source
end R1Z.PV_CB_Op84Exact
