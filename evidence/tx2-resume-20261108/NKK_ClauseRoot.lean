import NKK_ClausesRun
import NJU_ResumeRoot
set_option autoImplicit false
noncomputable section
namespace NKK_ClauseRoot
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission

/-- Complete SAME-argument child clauses on the actual source invocation.
This is source/callee installation, NOT the assembled native resume row. -/
theorem source (reservation : NP6_StdModel.Reservation) {H : Type}
 (d : AspisR1Stage2.aspis_core.digest.Digest32 H)
 (ck proof pub : Slice U8) (v : transport.Variant) (hash : H) :
 NKK_LogClauses.Holds (NKK_Clauses.Clause reservation d hash)
   (NJU_ResumeObserved.run reservation d ck proof pub v hash) ∧
 (NJU_ResumeObserved.run reservation d ck proof pub v hash).result=
 NJC_RawCalls.resume (NJC_FilledClause.reserved reservation) d ck proof pub v hash :=
 ⟨NKK_ResumeClauses.run reservation d ck proof pub v hash,
  NJU_ResumeRoot.source reservation d ck proof pub v hash⟩

/-- Exact cohort transport, on the SAME source log and Reservation. Native
cuts and parent G still must be attached before composed-row credit. -/
theorem cohort (reservation : NP6_StdModel.Reservation) {H : Type}
 (d : AspisR1Stage2.aspis_core.digest.Digest32 H)
 (ck proof pub : Slice U8) (hash : H) :
 NKK_LogClauses.Holds (NKK_Clauses.Clause reservation d hash)
   (NJU_ResumeObserved.run reservation d ck proof pub .S2 hash) ∧
 NIL_StatePort.reply (NJU_ResumeObserved.run reservation d ck proof pub .S2 hash).result=
 AspisR1Stage2.verifier.resumeWithOps
 (CheckpointBytes4Ops.ops (NJC_FilledClause.reserved reservation)) d ck proof pub .S2 hash :=
 ⟨NKK_ResumeClauses.run reservation d ck proof pub .S2 hash,
  NJU_ResumeRoot.cohort reservation d ck proof pub hash⟩

#print source
#print cohort
#print axioms source
#print axioms cohort
end NKK_ClauseRoot
