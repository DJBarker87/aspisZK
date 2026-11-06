import NKK_QueryStage
import NKK_Try
set_option autoImplicit false
noncomputable section
namespace NKK_QueryEndJoin
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission NJU_ResumeObserved
def next (reservation : NP6_StdModel.Reservation) {H : Type}
 (d : AspisR1Stage2.aspis_core.digest.Digest32 H) (bytes : Slice U8)
 (v : transport.Variant) (i4 : U8) (end1 : Usize)
 (state a3 a4 : Array U8 32#usize) (val val1 val2 val3 : E) (val4 : K)
 (i8 i9 i10 i11 i12 i13 i14 i15 i16 i17 i18 i19 i20 i21 i22 i23 : U32) : List U32 × verifier.Reader →
 NJU_Log.Run Event (core.result.Result (verifier.Prepared × verifier.Accumulator) verifier.Error)
 | ([q0,q1,q2,q3,q4,q5],last) => do
   let queries := Array.make 22#usize [i8,i9,i10,i11,i12,i13,i14,i15,i16,i17,i18,i19,i20,i21,i22,i23,q0,q1,q2,q3,q4,q5]
   let reply ← recordValidate queries
   NKK_Try.emitted reply (fun _=>finishTailG reservation d bytes v i4 end1 state a3 a4 val val1 val2 val3 val4 queries last)
 | _ => liftM (Result.fail .panic)

/-- SAME native query window feeds the literal next source continuation. -/
theorem source (reservation : NP6_StdModel.Reservation) {H : Type}
 (d : AspisR1Stage2.aspis_core.digest.Digest32 H) (bytes : Slice U8)
 (v : transport.Variant) (i4 : U8) (end1 : Usize)
 (state a3 a4 : Array U8 32#usize) (val val1 val2 val3 : E) (val4 : K)
 (i8 i9 i10 i11 i12 i13 i14 i15 i16 i17 i18 i19 i20 i21 i22 i23 : U32) (r : verifier.Reader) :
 queryEndG reservation d bytes v i4 end1 state a3 a4 val val1 val2 val3 val4 i8 i9 i10 i11 i12 i13 i14 i15 i16 i17 i18 i19 i20 i21 i22 i23 r=
 (NKK_QueryStage.model6 r >>= next reservation d bytes v i4 end1 state a3 a4 val val1 val2 val3 val4 i8 i9 i10 i11 i12 i13 i14 i15 i16 i17 i18 i19 i20 i21 i22 i23) := by
 rw [NKK_QueryStage.stage6]
 unfold queryEndG NKK_QueryStage.source6 next
 simp only [lift,NKK_LogReduce.lift_ok_bind,NKK_LogAlgebra.bind_assoc,NKK_LogReduce.pure_bind,NJU_Log.prod_cases]
 apply NKK_LogAlgebra.bind_congr
 rintro ⟨b0,r0⟩
 apply NKK_LogAlgebra.bind_congr
 rintro ⟨b1,r1⟩
 apply NKK_LogAlgebra.bind_congr
 rintro ⟨b2,r2⟩
 apply NKK_LogAlgebra.bind_congr
 rintro ⟨b3,r3⟩
 apply NKK_LogAlgebra.bind_congr
 rintro ⟨b4,r4⟩
 apply NKK_LogAlgebra.bind_congr
 rintro ⟨b5,r5⟩
 apply NKK_LogAlgebra.bind_congr
 intro reply
 cases reply <;> rfl

#print axioms source
end NKK_QueryEndJoin
