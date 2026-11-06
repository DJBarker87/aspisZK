import NKE_ResumeProgram1
set_option autoImplicit false
noncomputable section
namespace NKE_ResumeProgram
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission NJU_ResumeObserved

def queryEndG (reservation : NP6_StdModel.Reservation) {H : Type}
 (d : AspisR1Stage2.aspis_core.digest.Digest32 H) (bytes : Slice U8)
 (v : transport.Variant) (i4 : U8) (end1 : Usize)
 (state a3 a4 : Array U8 32#usize) (val val1 val2 val3 : E) (val4 : K)
 (i8 i9 i10 i11 i12 i13 i14 i15 i16 i17 i18 i19 i20 i21 i22 i23 : U32) (r28 : verifier.Reader) : NKE_Free.Program Event (core.result.Result (verifier.Prepared × verifier.Accumulator) verifier.Error) := do
 let (a21, r29) ←
   recordRaw 4#usize r28
 let i24 ← lift (core.num.U32.from_le_bytes a21)
 let (a22, r30) ←
   recordRaw 4#usize r29
 let i25 ← lift (core.num.U32.from_le_bytes a22)
 let (a23, r31) ←
   recordRaw 4#usize r30
 let i26 ← lift (core.num.U32.from_le_bytes a23)
 let (a24, r32) ←
   recordRaw 4#usize r31
 let i27 ← lift (core.num.U32.from_le_bytes a24)
 let (a25, r33) ←
   recordRaw 4#usize r32
 let i28 ← lift (core.num.U32.from_le_bytes a25)
 let (a26, r34) ←
   recordRaw 4#usize r33
 let i29 ← lift (core.num.U32.from_le_bytes a26)
 let queryValues := (Array.make 22#usize [
       i8, i9, i10, i11, i12, i13, i14, i15, i16,
       i17, i18, i19, i20, i21, i22, i23, i24,
       i25, i26, i27, i28, i29
       ])
 let r35 ←
   recordValidate
     queryValues
 let cf5 ←
   core.result.Result.Insts.CoreOpsTry.branch r35
 match cf5 with
 | core.ops.control_flow.ControlFlow.Continue _ =>
   finishTailG reservation d bytes v i4 end1 state a3 a4 val val1 val2 val3 val4 queryValues r34
 | core.ops.control_flow.ControlFlow.Break
   residual =>
   core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
     (verifier.Prepared × verifier.Accumulator)
     (core.convert.FromSame verifier.Error)
     residual

end NKE_ResumeProgram
