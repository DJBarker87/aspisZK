import NJU_ResumeErase
import NJU_ResumeReference
set_option autoImplicit false
noncomputable section
namespace NJU_ResumeRoot
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission
/-- One source-ordered execution with full replies and error/abort prefixes.
This erasure is source transport; native cut association is a separate obligation. -/
theorem source (reservation : NP6_StdModel.Reservation) {H : Type}
 (d : AspisR1Stage2.aspis_core.digest.Digest32 H)
 (ck proof pub : Slice U8) (v : transport.Variant) (hash : H) :
 (NJU_ResumeObserved.run reservation d ck proof pub v hash).result=
 NJC_RawCalls.resume (NJC_FilledClause.reserved reservation) d ck proof pub v hash :=
 (NJU_ResumeErase.header reservation d ck proof pub v hash).trans
 (NJU_ResumeReference.source reservation d ck proof pub v hash)
theorem cohort (reservation : NP6_StdModel.Reservation) {H : Type}
 (d : AspisR1Stage2.aspis_core.digest.Digest32 H)
 (ck proof pub : Slice U8) (hash : H) :
 NIL_StatePort.reply (NJU_ResumeObserved.run reservation d ck proof pub .S2 hash).result=
 AspisR1Stage2.verifier.resumeWithOps
 (CheckpointBytes4Ops.ops (NJC_FilledClause.reserved reservation)) d ck proof pub .S2 hash := by
 rw [source]
 exact NJC_RawCalls.source _ d ck proof pub hash
#print source
#print cohort
#print axioms source
#print axioms cohort
end NJU_ResumeRoot
