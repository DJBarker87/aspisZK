import NKK_ClausesQueryMid
set_option autoImplicit false
noncomputable section
namespace NKK_ResumeClauses
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission NJU_ResumeObserved

theorem queryBlock (reservation : NP6_StdModel.Reservation) {H : Type}
 (d : AspisR1Stage2.aspis_core.digest.Digest32 H) (bytes : Slice U8)
 (v : transport.Variant) (i4 : U8) (end1 : Usize)
 (state a3 a4 : Array U8 32#usize) (val val1 val2 val3 : E) (val4 : K)
 (r12 : verifier.Reader) (hash : H) :
 NKK_LogClauses.Holds (NKK_Clauses.Clause reservation d hash) (queryBlockG reservation d bytes v i4 end1 state a3 a4 val val1 val2 val3 val4 r12) := by
 unfold queryBlockG
 simp only [lift,NKK_LogReduce.lift_ok_bind]
 apply NKK_LogClauses.bind
 · exact NKK_Clauses.raw reservation d hash _ _
 · rintro ⟨a5,r13⟩
   apply NKK_LogClauses.bind
   · exact NKK_Clauses.raw reservation d hash _ _
   · rintro ⟨a6,r14⟩
     apply NKK_LogClauses.bind
     · exact NKK_Clauses.raw reservation d hash _ _
     · rintro ⟨a7,r15⟩
       apply NKK_LogClauses.bind
       · exact NKK_Clauses.raw reservation d hash _ _
       · rintro ⟨a8,r16⟩
         apply NKK_LogClauses.bind
         · exact NKK_Clauses.raw reservation d hash _ _
         · rintro ⟨a9,r17⟩
           apply NKK_LogClauses.bind
           · exact NKK_Clauses.raw reservation d hash _ _
           · rintro ⟨a10,r18⟩
             apply NKK_LogClauses.bind
             · exact NKK_Clauses.raw reservation d hash _ _
             · rintro ⟨a11,r19⟩
               apply NKK_LogClauses.bind
               · exact NKK_Clauses.raw reservation d hash _ _
               · rintro ⟨a12,r20⟩
                 apply queryMid

#print axioms queryBlock
end NKK_ResumeClauses
