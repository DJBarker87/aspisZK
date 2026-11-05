import NIY_C_QueryCut
import NIL_SectionPorts
set_option autoImplicit false
noncomputable section
namespace NIY_C_ValidationCut
open Aeneas Aeneas.Std Result ControlFlow Error AspisR1Stage2

def afterValidation (ops : ResumeOps)
 (bytes : Slice U8) (v : transport.Variant) (end1 : Usize) (i4 : U8)
 (state : Array U8 32#usize) (a3 : Array U8 32#usize) (a4 : Array U8 32#usize) (val : aspis_core.field.wide_exact.WideExact) (val1 : aspis_core.field.wide_exact.WideExact) (val2 : aspis_core.field.wide_exact.WideExact) (val3 : aspis_core.field.wide_exact.WideExact) (val4 : aspis_core.field.QM31) (queries : Array U32 22#usize) (r34 : verifier.Reader) :
 Result (core.result.Result (verifier.Prepared × verifier.Accumulator) verifier.Error) := do
 let r36 ←
   ops.readSemanticAlpha bytes
     r34.«at»
 let cf6 ←
   core.result.Result.Insts.CoreOpsTry.branch
     r36
 match cf6 with
 | core.ops.control_flow.ControlFlow.Continue
   val5 =>
   let (semantic_alpha, at1) := val5
   let (r37, r38) ←
     ops.readK
       { r34 with «at» := at1 }
   let cf7 ←
     core.result.Result.Insts.CoreOpsTry.branch
       r37
   match cf7 with
   | core.ops.control_flow.ControlFlow.Continue
     val6 =>
     let (r39, r40) ← ops.readK r38
     let cf8 ←
       core.result.Result.Insts.CoreOpsTry.branch
         r39
     match cf8 with
     |
       core.ops.control_flow.ControlFlow.Continue
       val7 =>
       let (r41, r42) ← ops.readK r40
       let cf9 ←
         core.result.Result.Insts.CoreOpsTry.branch
           r41
       match cf9 with
       |
         core.ops.control_flow.ControlFlow.Continue
         val8 =>
         let (r43, r44) ←
           ops.readK r42
         let cf10 ←
           core.result.Result.Insts.CoreOpsTry.branch
             r43
         match cf10 with
         |
           core.ops.control_flow.ControlFlow.Continue
           val9 =>
           let (r45, r46) ←
             ops.readE r44
           let cf11 ←
             core.result.Result.Insts.CoreOpsTry.branch
               r45
           match cf11 with
           |
             core.ops.control_flow.ControlFlow.Continue
             val10 =>
             let (r47, r48) ←
               ops.readE r46
             let cf12 ←
               core.result.Result.Insts.CoreOpsTry.branch
                 r47
             match cf12 with
             |
               core.ops.control_flow.ControlFlow.Continue
               val11 =>
               let (r49, r50) ←
                 ops.readK r48
               let cf13 ←
                 core.result.Result.Insts.CoreOpsTry.branch
                   r49
               match cf13 with
               |
                 core.ops.control_flow.ControlFlow.Continue
                 val12 =>
                 let i30 ←
                   ops.finalLen v
                 let q ←
                   ops.zeroK
                 let r52 ← ops.filled i30 q
                 let cf14 ←
                   core.result.Result.Insts.CoreOpsTry.branch
                     r52
                 match cf14 with
                 |
                   core.ops.control_flow.ControlFlow.Continue
                   val13 =>
                   let r53 ←
                     ops.readWeights
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
                              queries,
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

theorem source (ops : ResumeOps)
 (bytes : Slice U8) (v : transport.Variant) (end1 : Usize) (i4 : U8)
 (state : Array U8 32#usize) (a3 : Array U8 32#usize) (a4 : Array U8 32#usize) (val : aspis_core.field.wide_exact.WideExact) (val1 : aspis_core.field.wide_exact.WideExact) (val2 : aspis_core.field.wide_exact.WideExact) (val3 : aspis_core.field.wide_exact.WideExact) (val4 : aspis_core.field.QM31) (queries : Array U32 22#usize) (r34 : verifier.Reader) :
 NIY_C_QueryCut.afterQueries ops bytes v end1 i4 state a3 a4 val val1 val2 val3 val4 queries r34=
 (do let reply ← ops.validate queries
     NIL_TryTransport.cohort reply (fun _=>afterValidation ops bytes v end1 i4 state a3 a4 val val1 val2 val3 val4 queries r34)) := by
 unfold NIY_C_QueryCut.afterQueries
 apply NIL_ResultCases.bind_congr
 intro reply
 cases reply <;> rfl
#print axioms source
end NIY_C_ValidationCut
