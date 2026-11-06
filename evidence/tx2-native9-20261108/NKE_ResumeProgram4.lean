import NKE_ResumeProgram3
set_option autoImplicit false
noncomputable section
namespace NKE_ResumeProgram
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission NJU_ResumeObserved

def queryBlockG (reservation : NP6_StdModel.Reservation) {H : Type}
 (d : AspisR1Stage2.aspis_core.digest.Digest32 H) (bytes : Slice U8)
 (v : transport.Variant) (i4 : U8) (end1 : Usize)
 (state a3 a4 : Array U8 32#usize) (val val1 val2 val3 : E) (val4 : K)
 (r12 : verifier.Reader) : NKE_Free.Program Event (core.result.Result (verifier.Prepared × verifier.Accumulator) verifier.Error) := do
 let (a5, r13) ← recordRaw 4#usize r12
 let i8 ← lift (core.num.U32.from_le_bytes a5)
 let (a6, r14) ← recordRaw 4#usize r13
 let i9 ← lift (core.num.U32.from_le_bytes a6)
 let (a7, r15) ← recordRaw 4#usize r14
 let i10 ← lift (core.num.U32.from_le_bytes a7)
 let (a8, r16) ← recordRaw 4#usize r15
 let i11 ← lift (core.num.U32.from_le_bytes a8)
 let (a9, r17) ← recordRaw 4#usize r16
 let i12 ← lift (core.num.U32.from_le_bytes a9)
 let (a10, r18) ←
   recordRaw 4#usize r17
 let i13 ← lift (core.num.U32.from_le_bytes a10)
 let (a11, r19) ←
   recordRaw 4#usize r18
 let i14 ← lift (core.num.U32.from_le_bytes a11)
 let (a12, r20) ←
   recordRaw 4#usize r19
 let i15 ← lift (core.num.U32.from_le_bytes a12)
 queryMidG reservation d bytes v i4 end1 state a3 a4 val val1 val2 val3 val4 i8 i9 i10 i11 i12 i13 i14 i15 r20

end NKE_ResumeProgram
