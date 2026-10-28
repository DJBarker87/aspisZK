import PV_B3P_ByteChunk226
open Aeneas Aeneas.Std Result ControlFlow Error
set_option maxRecDepth 2048
set_option maxHeartbeats 1000000
namespace PV_B3P_226
def reference226.encode_owned
  (p : reference226.OwnedPublic) :
  Result (core.result.Result ((Array (Array Std.U8 64#usize) 23#usize) ×
    Std.Usize) aspis_core.state_only_prefix.r0.Error)
  := do
  let (b, n) ←
    if p.withdrawal
    then ok (true, 1427#usize)
    else ok (false, 1455#usize)
  let r ← reference226.chunk { p with withdrawal := b } 0#usize
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let r1 ← reference226.chunk { p with withdrawal := b } 64#usize
    let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue val1 =>
      let r2 ← reference226.chunk { p with withdrawal := b } 128#usize
      let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
      match cf2 with
      | core.ops.control_flow.ControlFlow.Continue val2 =>
        let r3 ← reference226.chunk { p with withdrawal := b } 192#usize
        let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r3
        match cf3 with
        | core.ops.control_flow.ControlFlow.Continue val3 =>
          let r4 ← reference226.chunk { p with withdrawal := b } 256#usize
          let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r4
          match cf4 with
          | core.ops.control_flow.ControlFlow.Continue val4 =>
            let r5 ← reference226.chunk { p with withdrawal := b } 320#usize
            let cf5 ← core.result.Result.Insts.CoreOpsTry.branch r5
            match cf5 with
            | core.ops.control_flow.ControlFlow.Continue val5 =>
              let r6 ←
                reference226.chunk { p with withdrawal := b } 384#usize
              let cf6 ← core.result.Result.Insts.CoreOpsTry.branch r6
              match cf6 with
              | core.ops.control_flow.ControlFlow.Continue val6 =>
                let r7 ←
                  reference226.chunk { p with withdrawal := b } 448#usize
                let cf7 ← core.result.Result.Insts.CoreOpsTry.branch r7
                match cf7 with
                | core.ops.control_flow.ControlFlow.Continue val7 =>
                  let r8 ←
                    reference226.chunk { p with withdrawal := b } 512#usize
                  let cf8 ← core.result.Result.Insts.CoreOpsTry.branch r8
                  match cf8 with
                  | core.ops.control_flow.ControlFlow.Continue val8 =>
                    let r9 ←
                      reference226.chunk { p with withdrawal := b } 576#usize
                    let cf9 ← core.result.Result.Insts.CoreOpsTry.branch r9
                    match cf9 with
                    | core.ops.control_flow.ControlFlow.Continue val9 =>
                      let r10 ←
                        reference226.chunk { p with withdrawal := b } 640#usize
                      let cf10 ←
                        core.result.Result.Insts.CoreOpsTry.branch r10
                      match cf10 with
                      | core.ops.control_flow.ControlFlow.Continue val10 =>
                        let r11 ←
                          reference226.chunk { p with withdrawal := b }
                            704#usize
                        let cf11 ←
                          core.result.Result.Insts.CoreOpsTry.branch r11
                        match cf11 with
                        | core.ops.control_flow.ControlFlow.Continue val11 =>
                          let r12 ←
                            reference226.chunk { p with withdrawal := b }
                              768#usize
                          let cf12 ←
                            core.result.Result.Insts.CoreOpsTry.branch r12
                          match cf12 with
                          | core.ops.control_flow.ControlFlow.Continue val12 =>
                            let r13 ←
                              reference226.chunk { p with withdrawal := b }
                                832#usize
                            let cf13 ←
                              core.result.Result.Insts.CoreOpsTry.branch r13
                            match cf13 with
                            | core.ops.control_flow.ControlFlow.Continue val13
                              =>
                              let r14 ←
                                reference226.chunk { p with withdrawal := b }
                                  896#usize
                              let cf14 ←
                                core.result.Result.Insts.CoreOpsTry.branch r14
                              match cf14 with
                              | core.ops.control_flow.ControlFlow.Continue
                                val14 =>
                                let r15 ←
                                  reference226.chunk { p with withdrawal := b }
                                    960#usize
                                let cf15 ←
                                  core.result.Result.Insts.CoreOpsTry.branch
                                    r15
                                match cf15 with
                                | core.ops.control_flow.ControlFlow.Continue
                                  val15 =>
                                  let r16 ←
                                    reference226.chunk
                                      { p with withdrawal := b } 1024#usize
                                  let cf16 ←
                                    core.result.Result.Insts.CoreOpsTry.branch
                                      r16
                                  match cf16 with
                                  | core.ops.control_flow.ControlFlow.Continue
                                    val16 =>
                                    let r17 ←
                                      reference226.chunk
                                        { p with withdrawal := b } 1088#usize
                                    let cf17 ←
                                      core.result.Result.Insts.CoreOpsTry.branch
                                        r17
                                    match cf17 with
                                    |
                                      core.ops.control_flow.ControlFlow.Continue
                                      val17 =>
                                      let r18 ←
                                        reference226.chunk
                                          { p with withdrawal := b } 1152#usize
                                      let cf18 ←
                                        core.result.Result.Insts.CoreOpsTry.branch
                                          r18
                                      match cf18 with
                                      |
                                        core.ops.control_flow.ControlFlow.Continue
                                        val18 =>
                                        let r19 ←
                                          reference226.chunk
                                            { p with withdrawal := b }
                                            1216#usize
                                        let cf19 ←
                                          core.result.Result.Insts.CoreOpsTry.branch
                                            r19
                                        match cf19 with
                                        |
                                          core.ops.control_flow.ControlFlow.Continue
                                          val19 =>
                                          let r20 ←
                                            reference226.chunk
                                              { p with withdrawal := b }
                                              1280#usize
                                          let cf20 ←
                                            core.result.Result.Insts.CoreOpsTry.branch
                                              r20
                                          match cf20 with
                                          |
                                            core.ops.control_flow.ControlFlow.Continue
                                            val20 =>
                                            let r21 ←
                                              reference226.chunk
                                                { p with withdrawal := b }
                                                1344#usize
                                            let cf21 ←
                                              core.result.Result.Insts.CoreOpsTry.branch
                                                r21
                                            match cf21 with
                                            |
                                              core.ops.control_flow.ControlFlow.Continue
                                              val21 =>
                                              let r22 ←
                                                reference226.chunk
                                                  { p with withdrawal := b }
                                                  1408#usize
                                              let cf22 ←
                                                core.result.Result.Insts.CoreOpsTry.branch
                                                  r22
                                              match cf22 with
                                              |
                                                core.ops.control_flow.ControlFlow.Continue
                                                val22 =>
                                                ok (core.result.Result.Ok
                                                  (Array.make 23#usize [
                                                     val, val1, val2, val3,
                                                     val4, val5, val6, val7,
                                                     val8, val9, val10, val11,
                                                     val12, val13, val14,
                                                     val15, val16, val17,
                                                     val18, val19, val20,
                                                     val21, val22
                                                     ], n))
                                              |
                                                core.ops.control_flow.ControlFlow.Break
                                                residual =>
                                                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                                  ((Array (Array Std.U8
                                                  64#usize) 23#usize) ×
                                                  Std.Usize)
                                                  (core.convert.FromSame
                                                  aspis_core.state_only_prefix.r0.Error)
                                                  residual
                                            |
                                              core.ops.control_flow.ControlFlow.Break
                                              residual =>
                                              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                                ((Array (Array Std.U8 64#usize)
                                                23#usize) × Std.Usize)
                                                (core.convert.FromSame
                                                aspis_core.state_only_prefix.r0.Error)
                                                residual
                                          |
                                            core.ops.control_flow.ControlFlow.Break
                                            residual =>
                                            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                              ((Array (Array Std.U8 64#usize)
                                              23#usize) × Std.Usize)
                                              (core.convert.FromSame
                                              aspis_core.state_only_prefix.r0.Error)
                                              residual
                                        |
                                          core.ops.control_flow.ControlFlow.Break
                                          residual =>
                                          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                            ((Array (Array Std.U8 64#usize)
                                            23#usize) × Std.Usize)
                                            (core.convert.FromSame
                                            aspis_core.state_only_prefix.r0.Error)
                                            residual
                                      | core.ops.control_flow.ControlFlow.Break
                                        residual =>
                                        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                          ((Array (Array Std.U8 64#usize)
                                          23#usize) × Std.Usize)
                                          (core.convert.FromSame
                                          aspis_core.state_only_prefix.r0.Error)
                                          residual
                                    | core.ops.control_flow.ControlFlow.Break
                                      residual =>
                                      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                        ((Array (Array Std.U8 64#usize)
                                        23#usize) × Std.Usize)
                                        (core.convert.FromSame
                                        aspis_core.state_only_prefix.r0.Error)
                                        residual
                                  | core.ops.control_flow.ControlFlow.Break
                                    residual =>
                                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                      ((Array (Array Std.U8 64#usize) 23#usize)
                                      × Std.Usize) (core.convert.FromSame
                                      aspis_core.state_only_prefix.r0.Error)
                                      residual
                                | core.ops.control_flow.ControlFlow.Break
                                  residual =>
                                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                    ((Array (Array Std.U8 64#usize) 23#usize)
                                    × Std.Usize) (core.convert.FromSame
                                    aspis_core.state_only_prefix.r0.Error)
                                    residual
                              | core.ops.control_flow.ControlFlow.Break
                                residual =>
                                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                  ((Array (Array Std.U8 64#usize) 23#usize) ×
                                  Std.Usize) (core.convert.FromSame
                                  aspis_core.state_only_prefix.r0.Error)
                                  residual
                            | core.ops.control_flow.ControlFlow.Break residual
                              =>
                              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                ((Array (Array Std.U8 64#usize) 23#usize) ×
                                Std.Usize) (core.convert.FromSame
                                aspis_core.state_only_prefix.r0.Error) residual
                          | core.ops.control_flow.ControlFlow.Break residual =>
                            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                              ((Array (Array Std.U8 64#usize) 23#usize) ×
                              Std.Usize) (core.convert.FromSame
                              aspis_core.state_only_prefix.r0.Error) residual
                        | core.ops.control_flow.ControlFlow.Break residual =>
                          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                            ((Array (Array Std.U8 64#usize) 23#usize) ×
                            Std.Usize) (core.convert.FromSame
                            aspis_core.state_only_prefix.r0.Error) residual
                      | core.ops.control_flow.ControlFlow.Break residual =>
                        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                          ((Array (Array Std.U8 64#usize) 23#usize) ×
                          Std.Usize) (core.convert.FromSame
                          aspis_core.state_only_prefix.r0.Error) residual
                    | core.ops.control_flow.ControlFlow.Break residual =>
                      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                        ((Array (Array Std.U8 64#usize) 23#usize) × Std.Usize)
                        (core.convert.FromSame
                        aspis_core.state_only_prefix.r0.Error) residual
                  | core.ops.control_flow.ControlFlow.Break residual =>
                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                      ((Array (Array Std.U8 64#usize) 23#usize) × Std.Usize)
                      (core.convert.FromSame
                      aspis_core.state_only_prefix.r0.Error) residual
                | core.ops.control_flow.ControlFlow.Break residual =>
                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                    ((Array (Array Std.U8 64#usize) 23#usize) × Std.Usize)
                    (core.convert.FromSame
                    aspis_core.state_only_prefix.r0.Error) residual
              | core.ops.control_flow.ControlFlow.Break residual =>
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                  ((Array (Array Std.U8 64#usize) 23#usize) × Std.Usize)
                  (core.convert.FromSame aspis_core.state_only_prefix.r0.Error)
                  residual
            | core.ops.control_flow.ControlFlow.Break residual =>
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                ((Array (Array Std.U8 64#usize) 23#usize) × Std.Usize)
                (core.convert.FromSame aspis_core.state_only_prefix.r0.Error)
                residual
          | core.ops.control_flow.ControlFlow.Break residual =>
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              ((Array (Array Std.U8 64#usize) 23#usize) × Std.Usize)
              (core.convert.FromSame aspis_core.state_only_prefix.r0.Error)
              residual
        | core.ops.control_flow.ControlFlow.Break residual =>
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            ((Array (Array Std.U8 64#usize) 23#usize) × Std.Usize)
            (core.convert.FromSame aspis_core.state_only_prefix.r0.Error)
            residual
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          ((Array (Array Std.U8 64#usize) 23#usize) × Std.Usize)
          (core.convert.FromSame aspis_core.state_only_prefix.r0.Error)
          residual
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        ((Array (Array Std.U8 64#usize) 23#usize) × Std.Usize)
        (core.convert.FromSame aspis_core.state_only_prefix.r0.Error) residual
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      ((Array (Array Std.U8 64#usize) 23#usize) × Std.Usize)
      (core.convert.FromSame aspis_core.state_only_prefix.r0.Error) residual


end PV_B3P_226
#print axioms PV_B3P_226.reference226.encode_owned
