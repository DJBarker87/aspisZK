import PV_B3P_ByteOutcome226V3
import PV_B3P_EncodeOutcome226V3
import PV_B3P_ProjectV3Law226
namespace PV_B3P_ReferenceOutcome226V3
open Aeneas Aeneas.Std PV_B3P_226V3
set_option autoImplicit false

theorem no_outer_failure (p : reference226.Source) :
    ∃ r, reference226.public_bytes p = .ok r := by
  rw [PV_B3P_ProjectV3Law226.complete_source]
  exact PV_B3P_EncodeOutcome226V3.no_outer_failure _
    (fun i => PV_B3P_ByteOutcome226V3.no_outer_failure _ i)

#print axioms no_outer_failure
end PV_B3P_ReferenceOutcome226V3
