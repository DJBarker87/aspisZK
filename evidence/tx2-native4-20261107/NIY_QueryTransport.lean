import NIY_QueryRead
import NIY_RawTransport
set_option autoImplicit false
noncomputable section
namespace NIY_QueryTransport
open Aeneas Aeneas.Std Result NIL_Carriers NIL_ResultTransport NIL_ResultReverse AspisR1
open NID_ResumeEmission

/-- Read22 transports the exact ordered array and reader to an arbitrary continuation.
Every primitive is one raw4 read; failures and divergence keep their original position. -/
theorem continuation {A B : Type} (f : A → B) (r12 : Fresh.R)
 (left : Array U32 22#usize → Fresh.R → Result A)
 (right : Array U32 22#usize → Cohort.R → Result B)
 (h : ∀ q out,outer f (left q (unReader out))=right q out) :
 outer f (do let (q,out) ← NIY_QueryRead.read22 (NIL_FreshOps.raw 4#usize) r12;left q out)=
 (do let (q,out) ← NIY_QueryRead.read22 (CheckpointBytes3Reader.raw 4#usize) (reader r12);right q out) := by
 have fresh := NIY_QueryRead.continuation (NIL_FreshOps.raw 4#usize) r12 left
 have cohort := NIY_QueryRead.continuation (CheckpointBytes3Reader.raw 4#usize) (reader r12) right
 apply Eq.trans (congrArg (outer f) fresh)
 apply Eq.trans ?_ cohort.symm
 apply NIY_RawTransport.raw
 intro a5 r13
 apply NIL_ResultCases.map_bind_congr
 intro i8
 apply NIY_RawTransport.raw
 intro a6 r14
 apply NIL_ResultCases.map_bind_congr
 intro i9
 apply NIY_RawTransport.raw
 intro a7 r15
 apply NIL_ResultCases.map_bind_congr
 intro i10
 apply NIY_RawTransport.raw
 intro a8 r16
 apply NIL_ResultCases.map_bind_congr
 intro i11
 apply NIY_RawTransport.raw
 intro a9 r17
 apply NIL_ResultCases.map_bind_congr
 intro i12
 apply NIY_RawTransport.raw
 intro a10 r18
 apply NIL_ResultCases.map_bind_congr
 intro i13
 apply NIY_RawTransport.raw
 intro a11 r19
 apply NIL_ResultCases.map_bind_congr
 intro i14
 apply NIY_RawTransport.raw
 intro a12 r20
 apply NIL_ResultCases.map_bind_congr
 intro i15
 apply NIY_RawTransport.raw
 intro a13 r21
 apply NIL_ResultCases.map_bind_congr
 intro i16
 apply NIY_RawTransport.raw
 intro a14 r22
 apply NIL_ResultCases.map_bind_congr
 intro i17
 apply NIY_RawTransport.raw
 intro a15 r23
 apply NIL_ResultCases.map_bind_congr
 intro i18
 apply NIY_RawTransport.raw
 intro a16 r24
 apply NIL_ResultCases.map_bind_congr
 intro i19
 apply NIY_RawTransport.raw
 intro a17 r25
 apply NIL_ResultCases.map_bind_congr
 intro i20
 apply NIY_RawTransport.raw
 intro a18 r26
 apply NIL_ResultCases.map_bind_congr
 intro i21
 apply NIY_RawTransport.raw
 intro a19 r27
 apply NIL_ResultCases.map_bind_congr
 intro i22
 apply NIY_RawTransport.raw
 intro a20 r28
 apply NIL_ResultCases.map_bind_congr
 intro i23
 apply NIY_RawTransport.raw
 intro a21 r29
 apply NIL_ResultCases.map_bind_congr
 intro i24
 apply NIY_RawTransport.raw
 intro a22 r30
 apply NIL_ResultCases.map_bind_congr
 intro i25
 apply NIY_RawTransport.raw
 intro a23 r31
 apply NIL_ResultCases.map_bind_congr
 intro i26
 apply NIY_RawTransport.raw
 intro a24 r32
 apply NIL_ResultCases.map_bind_congr
 intro i27
 apply NIY_RawTransport.raw
 intro a25 r33
 apply NIL_ResultCases.map_bind_congr
 intro i28
 apply NIY_RawTransport.raw
 intro a26 r34
 apply NIL_ResultCases.map_bind_congr
 intro i29
 exact h (Array.make 22#usize [i8, i9, i10, i11, i12, i13, i14, i15, i16, i17, i18, i19, i20, i21, i22, i23, i24, i25, i26, i27, i28, i29]) r34
#print axioms continuation
end NIY_QueryTransport
