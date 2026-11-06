import CheckpointBytes4Ops
import NLL_CallerCarrier
set_option autoImplicit false
noncomputable section
namespace NLL_ResumeQueries
open Aeneas Aeneas.Std Result AspisR1Stage2 AspisR1

theorem bounds (seen qs : List U32) (success : CheckpointBytes4Ops.queryLoop seen qs=.Ok ()) :
 ∀ q∈qs,q.val<262144 := by
 induction qs generalizing seen with
 | nil => intro q mem;cases mem
 | cons q qs ih =>
   unfold CheckpointBytes4Ops.queryLoop at success
   split at success
   · cases success
   · next good =>
     intro x member
     rcases List.mem_cons.mp member with rfl|later
     · have small := (not_or.mp good).1
       omega
     · exact ih (seen++[q]) success x later

/-- The actual resume validator discharges the primitive query range for its
SAME returned Prepared, including arbitrary incoming checkpoint bytes. No
checkpoint encoding or BodyMatches premise is needed for this local fact. -/
theorem returned (reserved : Bool) {X : Type} (D : aspis_core.digest.Digest32 X)
 (ck proof pub : Slice U8) (hash : X) (p : verifier.Prepared) (a : verifier.Accumulator)
 (success : verifier.resumeWithOps (CheckpointBytes4Ops.ops reserved) D ck proof pub .S2 hash=ok (.Ok (p,a))) :
 ∀ j,j<22 → p.queries.val[j]!.val<262144 := by
 obtain ⟨fields⟩:=CheckpointBytes4Ops.successful_fields reserved D ck proof pub .S2 hash p a success
 have valid:=fields.validate
 change ok (CheckpointBytes4Ops.queryLoop [] p.queries.val)=ok (.Ok ()) at valid
 have all:=bounds [] p.queries.val (Result.ok.inj valid)
 intro j hj
 have length : p.queries.val.length=22 := p.queries.property
 have within : j<p.queries.val.length := by omega
 have canonical:=all p.queries.val[j] (List.getElem_mem within)
 simpa only [List.getElem!_eq_getElem?_getD,List.getElem?_eq_getElem within,Option.getD_some] using canonical

set_option pp.proofs false
#print returned
#print axioms bounds
#print axioms returned
end NLL_ResumeQueries
end
