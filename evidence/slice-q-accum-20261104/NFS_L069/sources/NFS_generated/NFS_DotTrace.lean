import NFP_TraceHead
import NFP_DotInstall
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFS_DotTrace
open Aeneas Aeneas.Std Result AspisR1Stage2 NFP_QueryCuts Port3_NativeQueryBody
/-- Complete prefix observations, not just the successful dot value. -/
theorem head (ops : Ops) (proof : Slice U8) (p : verifier.Prepared)
 (a : verifier.Accumulator) (g : Array E 29#usize) (qPlace gPlace : Nat)
 (canonical : NEV_DotInputs.Canonical (FIp_DotsAdapter.toArray g)) :
 NFP_TraceHead.run (NFP_DotInstall.oracle ops qPlace gPlace) proof p a g =
 NFP_TraceHead.run (NFP_DotInstall.cohort ops) proof p a g := by
 simp only [NFP_TraceHead.run,NFP_DotInstall.oracle,NFP_DotInstall.cohort,
  NFP_ObserverErasure.erase,NFP_DotInstall.dot_result _ g qPlace gPlace canonical]
#print axioms head
end AspisR1.NFS_DotTrace
end
