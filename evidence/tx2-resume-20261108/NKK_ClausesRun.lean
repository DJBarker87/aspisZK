import NKK_ClausesResumeBody
set_option autoImplicit false
noncomputable section
namespace NKK_ResumeClauses
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission NJU_ResumeObserved

theorem run (reservation : NP6_StdModel.Reservation)
  {H : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H)
  (bytes : Slice Std.U8) (proof : Slice Std.U8) (public1 : Slice Std.U8)
  (v : transport.Variant) (hash : H) :
 NKK_LogClauses.Holds (NKK_Clauses.Clause reservation d hash) (run reservation d bytes proof public1 v hash) := by
 unfold run
 repeat' first
 | (apply resumeBody)
 | (apply queryBlock)
 | (apply queryMid)
 | (apply queryEnd)
 | (apply finishTail)
 | (apply NKK_Clauses.raw)
 | (apply NKK_Clauses.k)
 | (apply NKK_Clauses.e)
 | (apply NKK_Clauses.semantic)
 | (apply NKK_Clauses.weights)
 | (apply NKK_Clauses.validate)
 | (apply NKK_Clauses.filled)
 | (apply NKK_Clauses.headerAny)
 | (apply NKK_Clauses.digest)
 | (apply NKK_LogClauses.pure)
 | (apply NKK_LogClauses.lift)
 | (apply NKK_LogClauses.liftM)
 | (apply NKK_LogClauses.bind)
 | (apply NKK_LogClauses.branch)
 | (apply NKK_LogClauses.flow)
 | (intro value)
 | split
 | (cases_type Unit)

#print axioms run
end NKK_ResumeClauses
