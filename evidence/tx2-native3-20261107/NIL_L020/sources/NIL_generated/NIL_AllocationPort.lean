import NIL_FreshOps
set_option autoImplicit false
noncomputable section
namespace NIL_AllocationPort
open Aeneas Aeneas.Std Result NIL_Carriers NIL_FreshOps AspisR1
open NID_ResumeEmission

theorem source (reserved : Bool) {H : Type} (d : aspis_core.digest.Digest32 H)
 (n : Usize) (x : Fresh.K) :
 outer (NIL_Carriers.inner (vec k))
 (do let r ← NIL_FreshOps.filled reserved
       (aspis_core.field.QM31.Insts.CoreMarkerCopy (fun x=>ok x)) n x
     NIL_FreshOps.mapError (verifier.resume.closure_1.Insts.CoreOpsFunctionFnOnceTupleErrorError d) r ())=
 CheckpointBytes3Allocation.filled reserved n (k x) := by
 rw [CheckpointBytes3Allocation.filled_exact]
 cases reserved with
 | false => rfl
 | true =>
   change (ok (.Ok (vec k ⟨List.replicate n.val x,_⟩)) : Result (core.result.Result (alloc.vec.Vec Cohort.K) Cohort.Err))=_
   congr 2
   apply Subtype.ext
   exact List.map_replicate
#print axioms source
end NIL_AllocationPort
