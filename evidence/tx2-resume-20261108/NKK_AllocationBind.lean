import NKK_AllocationStage
import NKK_Try
import NKK_LogAlgebra
set_option autoImplicit false
noncomputable section
namespace NKK_AllocationBind
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission

/-- A failed SAME Reservation stops before the owned weights continuation,
preserving its one allocation event. No allocation-success premise. -/
theorem rejected {H T : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H)
 (err : NP6_StdModel.ReserveError)
 (next : alloc.vec.Vec NKK_AllocationStage.K →
 NJU_Log.Run NJU_ResumeObserved.Event (core.result.Result T verifier.Error)) :
 (NKK_AllocationStage.source (.Err err) d >>= fun reply=>NKK_Try.emitted reply next)=
 ⟨ok (.Err .Allocation),(NKK_AllocationStage.source (.Err err) d).events⟩ := rfl

#print axioms rejected
end NKK_AllocationBind
