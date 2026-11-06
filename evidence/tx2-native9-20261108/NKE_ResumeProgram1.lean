import NKE_ResumeProgramBase
set_option autoImplicit false
noncomputable section
namespace NKE_ResumeProgram
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission NJU_ResumeObserved

def finishTailG (reservation : NP6_StdModel.Reservation) {H : Type}
 (d : AspisR1Stage2.aspis_core.digest.Digest32 H) (bytes : Slice U8)
 (v : transport.Variant) (i4 : U8) (end1 : Usize)
 (state a3 a4 : Array U8 32#usize) (val val1 val2 val3 : E) (val4 : K)
 (queryValues : Array U32 22#usize) (r34 : verifier.Reader) : NKE_Free.Program Event (core.result.Result (verifier.Prepared × verifier.Accumulator) verifier.Error) := do
 let r36 ←
   recordSemantic bytes
     r34.«at»
 let cf6 ←
   core.result.Result.Insts.CoreOpsTry.branch
     r36
 match cf6 with
 | core.ops.control_flow.ControlFlow.Continue
   val5 =>
   let (semantic_alpha, at1) := val5
   let (r37, r38) ←
     recordK
       { r34 with «at» := at1 }
   let cf7 ←
     core.result.Result.Insts.CoreOpsTry.branch
       r37
   match cf7 with
   | core.ops.control_flow.ControlFlow.Continue
     val6 =>
     let (r39, r40) ← recordK r38
     let cf8 ←
       core.result.Result.Insts.CoreOpsTry.branch
         r39
     match cf8 with
     |
       core.ops.control_flow.ControlFlow.Continue
       val7 =>
       let (r41, r42) ← recordK r40
       let cf9 ←
         core.result.Result.Insts.CoreOpsTry.branch
           r41
       match cf9 with
       |
         core.ops.control_flow.ControlFlow.Continue
         val8 =>
         let (r43, r44) ←
           recordK r42
         let cf10 ←
           core.result.Result.Insts.CoreOpsTry.branch
             r43
         match cf10 with
         |
           core.ops.control_flow.ControlFlow.Continue
           val9 =>
           let (r45, r46) ←
             recordE r44
           let cf11 ←
             core.result.Result.Insts.CoreOpsTry.branch
               r45
           match cf11 with
           |
             core.ops.control_flow.ControlFlow.Continue
             val10 =>
             let (r47, r48) ←
               recordE r46
             let cf12 ←
               core.result.Result.Insts.CoreOpsTry.branch
                 r47
             match cf12 with
             |
               core.ops.control_flow.ControlFlow.Continue
               val11 =>
               let (r49, r50) ←
                 recordK r48
               let cf13 ←
                 core.result.Result.Insts.CoreOpsTry.branch
                   r49
               match cf13 with
               |
                 core.ops.control_flow.ControlFlow.Continue
                 val12 =>
                 let i30 ←
                   (fun v=>CheckpointBytes4Ops.finalLen (NIL_Carriers.variant v)) v
                 let q ←
                   (ok (NIL_Carriers.unK ⟨⟨0#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩))
                 let r51 ←
                   (recordFilled reservation)
                     (aspis_core.field.QM31.Insts.CoreMarkerCopy (fun x=>ok x))
                     i30 q
                 let r52 ←
                   NIL_FreshOps.mapError
                     (verifier.resume.closure_1.Insts.CoreOpsFunctionFnOnceTupleErrorError
                     (NIL_FreshOps.digest d))
                     r51 ()
                 let cf14 ←
                   core.result.Result.Insts.CoreOpsTry.branch
                     r52
                 match cf14 with
                 |
                   core.ops.control_flow.ControlFlow.Continue
                   val13 =>
                   let r53 ←
                     recordWeights
                       bytes r50.«at» val13
                   let cf15 ←
                     core.result.Result.Insts.CoreOpsTry.branch
                       r53
                   match cf15 with
                   |
                     core.ops.control_flow.ControlFlow.Continue
                     val14 =>
                     let (weights, at2) := val14
                     if at2 != end1
                     then
                       ok
                         (core.result.Result.Err
                         verifier.Error.Checkpoint)
                     else
                       let i31 ←
                         lift (UScalar.cast
                           .Usize i4)
                       ok (core.result.Result.Ok
                         ({
                            variant := v,
                            roots :=
                              (Array.make
                                 2#usize [
                                a3, a4
                                ]),
                            gamma := val,
                            kappa := val1,
                            alpha :=
                              (Array.make
                                 2#usize [
                                val2, val3
                                ]),
                            rho := val4,
                            queries :=
                              queryValues,
                            semantic_alpha,
                            z :=
                              (Array.make
                                 2#usize [
                                {
                                  x := val6,
                                  y := val7
                                },
                                {
                                  x := val8,
                                  y := val9
                                }
                                ]),
                            claim := val10,
                            state
                          },
                         {
                           weights,
                           rhs := val11,
                           power := val12,
                           next := i31
                         }))
                   |
                     core.ops.control_flow.ControlFlow.Break
                     residual =>
                     core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                       (verifier.Prepared ×
                       verifier.Accumulator)
                       (core.convert.FromSame
                       verifier.Error) residual
                 |
                   core.ops.control_flow.ControlFlow.Break
                   residual =>
                   core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                     (verifier.Prepared ×
                     verifier.Accumulator)
                     (core.convert.FromSame
                     verifier.Error) residual
               |
                 core.ops.control_flow.ControlFlow.Break
                 residual =>
                 core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                   (verifier.Prepared ×
                   verifier.Accumulator)
                   (core.convert.FromSame
                   verifier.Error) residual
             |
               core.ops.control_flow.ControlFlow.Break
               residual =>
               core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                 (verifier.Prepared ×
                 verifier.Accumulator)
                 (core.convert.FromSame
                 verifier.Error) residual
           |
             core.ops.control_flow.ControlFlow.Break
             residual =>
             core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
               (verifier.Prepared ×
               verifier.Accumulator)
               (core.convert.FromSame
               verifier.Error) residual
         |
           core.ops.control_flow.ControlFlow.Break
           residual =>
           core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
             (verifier.Prepared ×
             verifier.Accumulator)
             (core.convert.FromSame
             verifier.Error) residual
       | core.ops.control_flow.ControlFlow.Break
         residual =>
         core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
           (verifier.Prepared ×
           verifier.Accumulator)
           (core.convert.FromSame
           verifier.Error) residual
     | core.ops.control_flow.ControlFlow.Break
       residual =>
       core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
         (verifier.Prepared ×
         verifier.Accumulator)
         (core.convert.FromSame verifier.Error)
         residual
   | core.ops.control_flow.ControlFlow.Break
     residual =>
     core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
       (verifier.Prepared ×
       verifier.Accumulator)
       (core.convert.FromSame verifier.Error)
       residual
 | core.ops.control_flow.ControlFlow.Break
   residual =>
   core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
     (verifier.Prepared × verifier.Accumulator)
     (core.convert.FromSame verifier.Error)
     residual

end NKE_ResumeProgram
