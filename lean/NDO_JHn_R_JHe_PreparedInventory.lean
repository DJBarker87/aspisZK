import NDO_JHn_R_JHe_PreparedFields
import RPz7_WAdm_RunInventory
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHe_PreparedInventory
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open InstalledPreparation FirstComposition JGr_Geometry
abbrev query := SAQ_Decoder.install (JFr_TX2_DotsBinding.ops JGp_Seeds.query)
abbrev geometry := SAQ_Constructor.install () JGp_Seeds.geometry

theorem owner : WAdm_Domain.SessionAPrepare installed := by
  have h := SAP_PrepareOwner.installed
    (Op3I_Install.install (Op4P_Install.install
      (WAdm_Execution.base (JGp_Allocation.base (Op5T_Concrete.current JGp_Seeds.base)) true
        query geometry))) JGe_Boundaries.value (NP6_StdModel.calls (.Ok ()))
  rw [JGe_Boundaries.circle] at h
  exact h
#print axioms owner

theorem ports : Port5Q1_QueryPorts.SessionAPrimitives query :=
  SAQ_Decoder.primitives _
#print axioms ports
end AspisR1.JHe_PreparedInventory
end
