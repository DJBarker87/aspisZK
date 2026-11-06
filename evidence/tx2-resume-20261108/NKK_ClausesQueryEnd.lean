import NKK_ClausesFinishTail
set_option autoImplicit false
noncomputable section
namespace NKK_ResumeClauses
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission NJU_ResumeObserved

theorem queryEnd (reservation : NP6_StdModel.Reservation) {H : Type}
 (d : AspisR1Stage2.aspis_core.digest.Digest32 H) (bytes : Slice U8)
 (v : transport.Variant) (i4 : U8) (end1 : Usize)
 (state a3 a4 : Array U8 32#usize) (val val1 val2 val3 : E) (val4 : K)
 (i8 i9 i10 i11 i12 i13 i14 i15 i16 i17 i18 i19 i20 i21 i22 i23 : U32) (r28 : verifier.Reader) (hash : H) :
 NKK_LogClauses.Holds (NKK_Clauses.Clause reservation d hash) (queryEndG reservation d bytes v i4 end1 state a3 a4 val val1 val2 val3 val4 i8 i9 i10 i11 i12 i13 i14 i15 i16 i17 i18 i19 i20 i21 i22 i23 r28) := by
 unfold queryEndG
 repeat' first
 | (solve | (change List.Forall _ []; simp))
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

#print axioms queryEnd
end NKK_ResumeClauses
