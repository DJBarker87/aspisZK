import NKE_ResumeProgram4
set_option autoImplicit false
noncomputable section
namespace NKE_ResumeProgram
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission NJU_ResumeObserved

def resumeBodyG (reservation : NP6_StdModel.Reservation) {H : Type}
 (d : AspisR1Stage2.aspis_core.digest.Digest32 H) (bytes : Slice U8)
 (v : transport.Variant) (i4 : U8) (end1 : Usize) : NKE_Free.Program Event (core.result.Result (verifier.Prepared × verifier.Accumulator) verifier.Error) := do
 let (state, r) ←
   recordRaw 32#usize
     { bytes, «at» := 80#usize }
 let (a3, r1) ← recordRaw 32#usize r
 let (a4, r2) ← recordRaw 32#usize r1
 let (r3, r4) ← recordE r2
 let cf ← core.result.Result.Insts.CoreOpsTry.branch r3
 match cf with
 | core.ops.control_flow.ControlFlow.Continue val =>
   let (r5, r6) ← recordE r4
   let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r5
   match cf1 with
   | core.ops.control_flow.ControlFlow.Continue val1 =>
     let (r7, r8) ← recordE r6
     let cf2 ←
       core.result.Result.Insts.CoreOpsTry.branch r7
     match cf2 with
     | core.ops.control_flow.ControlFlow.Continue val2 =>
       let (r9, r10) ← recordE r8
       let cf3 ←
         core.result.Result.Insts.CoreOpsTry.branch r9
       match cf3 with
       | core.ops.control_flow.ControlFlow.Continue val3 =>
         let (r11, r12) ← recordK r10
         let cf4 ←
           core.result.Result.Insts.CoreOpsTry.branch r11
         match cf4 with
         | core.ops.control_flow.ControlFlow.Continue val4
           =>
           queryBlockG reservation d bytes v i4 end1 state a3 a4 val val1 val2 val3 val4 r12
         | core.ops.control_flow.ControlFlow.Break residual
           =>
           core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
             (verifier.Prepared × verifier.Accumulator)
             (core.convert.FromSame verifier.Error) residual
       | core.ops.control_flow.ControlFlow.Break residual =>
         core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
           (verifier.Prepared × verifier.Accumulator)
           (core.convert.FromSame verifier.Error) residual
     | core.ops.control_flow.ControlFlow.Break residual =>
       core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
         (verifier.Prepared × verifier.Accumulator)
         (core.convert.FromSame verifier.Error) residual
   | core.ops.control_flow.ControlFlow.Break residual =>
     core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
       (verifier.Prepared × verifier.Accumulator)
       (core.convert.FromSame verifier.Error) residual
 | core.ops.control_flow.ControlFlow.Break residual =>
   core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
     (verifier.Prepared × verifier.Accumulator)
     (core.convert.FromSame verifier.Error) residual

end NKE_ResumeProgram
