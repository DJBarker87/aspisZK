import NKU_Chronology
import NKK_AllocationStage
import NKK_AllocationBind
set_option autoImplicit false
noncomputable section
namespace NKU_Allocation
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission
open NKU_Chronology
def post (s : NKU.State) (owner : alloc.vec.Vec NKU.K) : NKU.State :=
 {s with phase := .weights,owned := some owner}
/-- The existing Allocator item supplies the SAME Reservation at this site.
No free Bool or successful-allocation premise is introduced. -/
def run {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H) : Stage Unit := fun s=>do
 let reply ← NKK_AllocationStage.source s.frame.reservation d
 NKK_Try.emitted reply (fun owner=>pure (.Ok ((),post s owner)))
theorem rejected {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H)
 (s : NKU.State) (err : NP6_StdModel.ReserveError) (same : s.frame.reservation=.Err err) :
 (run d s).result=.ok (.Err .Allocation) := by
 unfold run
 simp only [NJU_Log.erase_bind,same,NKK_AllocationStage.rejected]
 rfl
theorem frame (s : NKU.State) (owner : alloc.vec.Vec NKU.K) :
 (post s owner).frame=s.frame ∧ (post s owner).decoded=s.decoded ∧
 (post s owner).reader=s.reader := ⟨rfl,rfl,rfl⟩
#print axioms rejected
#print axioms frame
end NKU_Allocation
