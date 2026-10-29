import PV_B3P_Resume5Axioms
namespace PV_B3P_Resume5Focused
open Aeneas Aeneas.Std ProverRwFull
set_option autoImplicit false
noncomputable section
abbrev Types := PV_B3P_Carrier227.Types

theorem neighbouring_callbacks (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op224 (Types base) (PV_B3P_Install227.actual base ops)=@ExternalFuns.op224 (Types base) ops ∧
    @ExternalFuns.op226 (Types base) (PV_B3P_Install227.actual base ops)=@ExternalFuns.op226 (Types base) ops ∧
    @ExternalFuns.op228 (Types base) (PV_B3P_Install227.actual base ops)=@ExternalFuns.op228 (Types base) ops := by
  exact ⟨PV_B3P_Install227.preserved_op224 base ops PV_B3P_227.reference_terminal.reference227,
    PV_B3P_Install227.preserved_op226 base ops PV_B3P_227.reference_terminal.reference227,
    PV_B3P_Install227.preserved_op228 base ops PV_B3P_227.reference_terminal.reference227⟩

theorem retained_divergence : PV_B3P_Install227.transport .div = .div :=
  PV_B3P_Install227.div_tag

#print axioms neighbouring_callbacks
#print axioms retained_divergence
#print axioms PV_B3P_Resume5Combined.installed_complete
end
end PV_B3P_Resume5Focused
