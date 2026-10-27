import PV_B1_Install
set_option autoImplicit false
noncomputable section
namespace PV_B1_InstallStability
open Aeneas Aeneas.Std Result PV_B1_Host PV_B1_Install
variable [ExternalTypes]

theorem idempotent (ops : ExternalFuns) : selected (selected ops)=selected ops := rfl

theorem old_callbacks_removed (ops : ExternalFuns)
    (f : Slice HQ → Result (Option HQ))
    (g : (N : Usize) → HW → Result (Array HW N))
    (h : Rows → Array U16 64#usize → HQ → Result Bool) :
    selected {ops with op230:=f,op254:=g,op258:=h}=selected ops := rfl

theorem op134_preserved (ops : ExternalFuns) : (selected ops).op134=ops.op134 := rfl

theorem op259_preserved (ops : ExternalFuns) : (selected ops).op259=ops.op259 := rfl
#print axioms idempotent
#print axioms old_callbacks_removed
#print axioms op134_preserved
#print axioms op259_preserved
end PV_B1_InstallStability
