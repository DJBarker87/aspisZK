import PV_B3P_PartsBinding13227
namespace PV_B3P_InstalledFit13227
open Aeneas Aeneas.Std ProverRwFull PV_B3P_TopDown13227
set_option autoImplicit false
noncomputable section
/-- A bridge-hypothesis fit for the installed reference. This equality is an
installation law, NOT deployed Rust-to-reference association. A premise-removal
claim still needs all the native, D188, slice and std obligations. -/
theorem selected_callback (base : ExternalTypes)
    (original : @ExternalFuns (PV_B3P_Install227.Types base))
    (self : @host_semantic.SemanticOracle (PV_B3P_Install227.Types base))
    (point : Array aspis_core.field.QM31 10#usize) :
    letI : ExternalTypes := PV_B3P_Install227.Types base
    let ops := PV_B3P_Install227.actual base original
    let terminal := transported_reference base
    ∀ claims,
      ops.op227 self.«public» claims point self.challenges =
        terminal self.«public» claims point self.challenges := by
  letI : ExternalTypes := PV_B3P_Install227.Types base
  exact fun claims => PV_B3P_Install227.actual_source base original self.«public» claims point self.challenges
#print axioms selected_callback
end
end PV_B3P_InstalledFit13227
