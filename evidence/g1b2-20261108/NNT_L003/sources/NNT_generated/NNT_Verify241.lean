import NNT_Interfaces
import NNS_PortLaw241
set_option autoImplicit false
noncomputable section
namespace NNT_Verify241
open RSL

theorem verify_law (x : NMS_R2Replay241.VerifyArgs) (env : Env) :
 LIBB_Tx2Auth.law x.1 x.2.1 x.2.2 env (NMX_R7_Verify241.verify x env) := by
 unfold LIBB_Tx2Auth.law NMX_R7_Verify241.verify
 split
 · exact LIBB_ObservationModel.contains_graph env _ _ _
 · rfl
#print axioms verify_law
end NNT_Verify241
