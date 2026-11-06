import NKK_QueryStage
import NKK_Try
set_option autoImplicit false
noncomputable section
namespace NKK_QueryBlockJoin
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission NJU_ResumeObserved
def next (reservation : NP6_StdModel.Reservation) {H : Type}
 (d : AspisR1Stage2.aspis_core.digest.Digest32 H) (bytes : Slice U8)
 (v : transport.Variant) (i4 : U8) (end1 : Usize)
 (state a3 a4 : Array U8 32#usize) (val val1 val2 val3 : E) (val4 : K) : List U32 × verifier.Reader →
 NJU_Log.Run Event (core.result.Result (verifier.Prepared × verifier.Accumulator) verifier.Error)
 | ([q0,q1,q2,q3,q4,q5,q6,q7],last) => queryMidG reservation d bytes v i4 end1 state a3 a4 val val1 val2 val3 val4 q0 q1 q2 q3 q4 q5 q6 q7 last
 | _ => liftM (Result.fail .panic)

/-- SAME native query window feeds the literal next source continuation. -/
theorem source (reservation : NP6_StdModel.Reservation) {H : Type}
 (d : AspisR1Stage2.aspis_core.digest.Digest32 H) (bytes : Slice U8)
 (v : transport.Variant) (i4 : U8) (end1 : Usize)
 (state a3 a4 : Array U8 32#usize) (val val1 val2 val3 : E) (val4 : K) (r : verifier.Reader) :
 queryBlockG reservation d bytes v i4 end1 state a3 a4 val val1 val2 val3 val4  r=
 (NKK_QueryStage.model8 r >>= next reservation d bytes v i4 end1 state a3 a4 val val1 val2 val3 val4 ) := by
 rw [NKK_QueryStage.stage8]
 unfold queryBlockG NKK_QueryStage.source8 next
 simp only [lift,NKK_LogReduce.lift_ok_bind,NKK_LogAlgebra.bind_assoc,NKK_LogReduce.pure_bind,NJU_Log.prod_cases]

#print axioms source
end NKK_QueryBlockJoin
