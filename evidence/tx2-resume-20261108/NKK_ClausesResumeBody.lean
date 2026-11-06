import NKK_ClausesQueryBlock
set_option autoImplicit false
noncomputable section
namespace NKK_ResumeClauses
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission NJU_ResumeObserved

theorem resumeBody (reservation : NP6_StdModel.Reservation) {H : Type}
 (d : AspisR1Stage2.aspis_core.digest.Digest32 H) (bytes : Slice U8)
 (v : transport.Variant) (i4 : U8) (end1 : Usize) (hash : H) :
 NKK_LogClauses.Holds (NKK_Clauses.Clause reservation d hash) (resumeBodyG reservation d bytes v i4 end1) := by
 unfold resumeBodyG
 repeat' first
 | (solve | (change List.Forall _ []; simp))
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
 | (apply NKK_LogClauses.bind)
 | (apply NKK_LogClauses.branch)
 | (apply NKK_LogClauses.flow)
 | (intro value)
 | split
 | (cases_type Unit)

#print axioms resumeBody
end NKK_ResumeClauses
