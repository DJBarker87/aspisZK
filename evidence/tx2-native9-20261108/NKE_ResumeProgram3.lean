import NKE_ResumeProgram2
set_option autoImplicit false
noncomputable section
namespace NKE_ResumeProgram
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission NJU_ResumeObserved

def queryMidG (reservation : NP6_StdModel.Reservation) {H : Type}
 (d : AspisR1Stage2.aspis_core.digest.Digest32 H) (bytes : Slice U8)
 (v : transport.Variant) (i4 : U8) (end1 : Usize)
 (state a3 a4 : Array U8 32#usize) (val val1 val2 val3 : E) (val4 : K)
 (i8 i9 i10 i11 i12 i13 i14 i15 : U32) (r20 : verifier.Reader) : NKE_Free.Program Event (core.result.Result (verifier.Prepared × verifier.Accumulator) verifier.Error) := do
 let (a13, r21) ←
   recordRaw 4#usize r20
 let i16 ← lift (core.num.U32.from_le_bytes a13)
 let (a14, r22) ←
   recordRaw 4#usize r21
 let i17 ← lift (core.num.U32.from_le_bytes a14)
 let (a15, r23) ←
   recordRaw 4#usize r22
 let i18 ← lift (core.num.U32.from_le_bytes a15)
 let (a16, r24) ←
   recordRaw 4#usize r23
 let i19 ← lift (core.num.U32.from_le_bytes a16)
 let (a17, r25) ←
   recordRaw 4#usize r24
 let i20 ← lift (core.num.U32.from_le_bytes a17)
 let (a18, r26) ←
   recordRaw 4#usize r25
 let i21 ← lift (core.num.U32.from_le_bytes a18)
 let (a19, r27) ←
   recordRaw 4#usize r26
 let i22 ← lift (core.num.U32.from_le_bytes a19)
 let (a20, r28) ←
   recordRaw 4#usize r27
 let i23 ← lift (core.num.U32.from_le_bytes a20)
 queryEndG reservation d bytes v i4 end1 state a3 a4 val val1 val2 val3 val4 i8 i9 i10 i11 i12 i13 i14 i15 i16 i17 i18 i19 i20 i21 i22 i23 r28

end NKE_ResumeProgram
