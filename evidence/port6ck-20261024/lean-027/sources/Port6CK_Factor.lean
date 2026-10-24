import Port6CK_Queries
import Port4A_NativeReader
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port6CK_Factor
open Aeneas Aeneas.Std Result AspisR1Stage2
def tail (ops : ResumeOps) (bytes : Slice U8) (v : transport.Variant)
    (i4 : U8) (end1 : Usize) (s6 : Slice U8) (a2 : Array U8 32#usize) :
    Result (core.result.Result (verifier.Prepared × verifier.Accumulator) verifier.Error) := do
  let b4 ←
    ops.ne core.cmp.PartialEqU8
      s6 a2
  if b4
  then ok (core.result.Result.Err verifier.Error.Checkpoint)
  else
    let (state, r) ←
      ops.raw 32#usize
        { bytes, «at» := 80#usize }
    let (a3, r1) ← ops.raw 32#usize r
    let (a4, r2) ← ops.raw 32#usize r1
    let (r3, r4) ← ops.readE r2
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r3
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let (r5, r6) ← ops.readE r4
      let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r5
      match cf1 with
      | core.ops.control_flow.ControlFlow.Continue val1 =>
        let (r7, r8) ← ops.readE r6
        let cf2 ←
          core.result.Result.Insts.CoreOpsTry.branch r7
        match cf2 with
        | core.ops.control_flow.ControlFlow.Continue val2 =>
          let (r9, r10) ← ops.readE r8
          let cf3 ←
            core.result.Result.Insts.CoreOpsTry.branch r9
          match cf3 with
          | core.ops.control_flow.ControlFlow.Continue val3 =>
            let (r11, r12) ← ops.readK r10
            let cf4 ←
              core.result.Result.Insts.CoreOpsTry.branch r11
            match cf4 with
            | core.ops.control_flow.ControlFlow.Continue val4
              =>
              Port6CK_Queries.cps ops.raw r12 fun queries r34 => do
              let r35 ←
                ops.validate
                  queries
              let cf5 ←
                core.result.Result.Insts.CoreOpsTry.branch r35
              match cf5 with
              | core.ops.control_flow.ControlFlow.Continue _ =>
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
              | core.ops.control_flow.ControlFlow.Break
                residual =>
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                  (verifier.Prepared × verifier.Accumulator)
                  (core.convert.FromSame verifier.Error)
                  residual
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

/-- Literal current source decomposition at its22-query raw-read section. -/
theorem source (ops : ResumeOps) (bytes : Slice U8) (v : transport.Variant)
    (i4 : U8) (end1 : Usize) (s6 : Slice U8) (a2 : Array U8 32#usize) :
    Port4A_NativeReader.tail ops bytes v i4 end1 s6 a2=tail ops bytes v i4 end1 s6 a2 := by
  rfl

#print axioms source
end AspisR1.Port6CK_Factor
end
