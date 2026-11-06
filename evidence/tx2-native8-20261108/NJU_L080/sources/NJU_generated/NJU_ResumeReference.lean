import NJU_ResumeObserved
set_option autoImplicit false
noncomputable section
namespace NJU_ResumeReference
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission NJU_ResumeObserved

/-- Structural forward reference equality, proved by small bind/branch goals
rather than kernel reduction of the complete deep emitted term. -/
theorem source (reservation : NP6_StdModel.Reservation) {H : Type}
 (d : AspisR1Stage2.aspis_core.digest.Digest32 H)
 (ck proof pub : Slice U8) (v : transport.Variant) (hash : H) :
 runRef reservation d ck proof pub v hash=
 NJC_RawCalls.resume (NJC_FilledClause.reserved reservation) d ck proof pub v hash := by
 unfold runRef NJC_RawCalls.resume NID_ResumeEmission.verifier.resume
 repeat' first
 | (intro hypothesis)
 | (apply NIL_ResultCases.bind_congr; intro value)
 | (fail_if_no_progress simp_all [NJU_Log.prod_cases])
 | split
 | (unfold resumeBodyR)
 | (unfold queryBlockR)
 | (unfold queryMidR)
 | (unfold queryEndR)
 | (unfold finishTailR)
 | rfl

#print axioms source
end NJU_ResumeReference
