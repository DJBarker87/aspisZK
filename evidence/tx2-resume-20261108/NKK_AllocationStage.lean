import NJU_ResumeObserved
import NJR_ReservationSites
set_option autoImplicit false
noncomputable section
namespace NKK_AllocationStage
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission
abbrev K := aspis_core.field.QM31
def zero : K := ⟨⟨0#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩
def copy : core.marker.Copy K := aspis_core.field.QM31.Insts.CoreMarkerCopy (fun x=>ok x)

def source (reservation : NP6_StdModel.Reservation) {H : Type}
 (d : AspisR1Stage2.aspis_core.digest.Digest32 H) :
 NJU_Log.Run NJU_ResumeObserved.Event (core.result.Result (alloc.vec.Vec K) verifier.Error) := do
 let reply ← NJU_ResumeObserved.recordFilled reservation copy 64#usize zero
 NIL_FreshOps.mapError
  (verifier.resume.closure_1.Insts.CoreOpsFunctionFnOnceTupleErrorError (NIL_FreshOps.digest d)) reply ()

/-- Actual source allocation event, with this SAME Reservation, size and ZERO
value. Error mapping adds no child event or independent allocator outcome. -/
theorem events (reservation : NP6_StdModel.Reservation) {H : Type}
 (d : AspisR1Stage2.aspis_core.digest.Digest32 H) :
 (source reservation d).events=[.filled 64#usize zero
 (NIL_FreshOps.filled (NJC_FilledClause.reserved reservation) copy 64#usize zero)] := by
 cases reservation with
 | Ok unit => cases unit;rfl
 | Err err => rfl

/-- Allocation rejection is the exact source Error, with no native success
premise and no suffix parser/Box event. -/
theorem rejected (err : NP6_StdModel.ReserveError) {H : Type}
 (d : AspisR1Stage2.aspis_core.digest.Digest32 H) :
 (source (.Err err) d).result=ok (.Err .Allocation) := rfl

#print axioms events
#print axioms rejected
end NKK_AllocationStage
