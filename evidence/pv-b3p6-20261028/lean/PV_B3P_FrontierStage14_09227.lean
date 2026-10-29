import PV_B3P_FrontierStage14_10227
namespace PV_B3P_FrontierStages14227
open Aeneas Aeneas.Std PV_B3P_Missing14Frontier
set_option autoImplicit false
def suffix9_14 (fields : FF14) (out : alloc.vec.Vec U8) (values : FV14) : Result FS14 := do
  let a9 ← Array.index_usize values 9#usize
  let s9 ← lift (Array.to_slice a9)
  let (r9, out10) ← fields out s9
  let cf9 ← core.result.Result.Insts.CoreOpsTry.branch r9
  match cf9 with
  | core.ops.control_flow.ControlFlow.Continue _ =>
    let a10 ← Array.index_usize values 10#usize
    let s10 ← lift (Array.to_slice a10)
    let (r10, out11) ← fields out10 s10
    let cf10 ←
      core.result.Result.Insts.CoreOpsTry.branch r10
    match cf10 with
    | core.ops.control_flow.ControlFlow.Continue _ =>
      let a11 ← Array.index_usize values 11#usize
      let s11 ← lift (Array.to_slice a11)
      let (r11, out12) ← fields out11 s11
      let cf11 ←
        core.result.Result.Insts.CoreOpsTry.branch r11
      match cf11 with
      | core.ops.control_flow.ControlFlow.Continue _ =>
        let a12 ← Array.index_usize values 12#usize
        let s12 ← lift (Array.to_slice a12)
        let (r12, out13) ← fields out12 s12
        let cf12 ←
          core.result.Result.Insts.CoreOpsTry.branch r12
        match cf12 with
        | core.ops.control_flow.ControlFlow.Continue _ =>
          let a13 ← Array.index_usize values 13#usize
          let s13 ← lift (Array.to_slice a13)
          let (r13, out14) ← fields out13 s13
          let cf13 ←
            core.result.Result.Insts.CoreOpsTry.branch r13
          match cf13 with
          | core.ops.control_flow.ControlFlow.Continue _ =>
            let a14 ← Array.index_usize values 14#usize
            let s14 ← lift (Array.to_slice a14)
            let (r14, out15) ← fields out14 s14
            let cf14 ←
              core.result.Result.Insts.CoreOpsTry.branch r14
            match cf14 with
            | core.ops.control_flow.ControlFlow.Continue _ =>
              let a15 ← Array.index_usize values 15#usize
              let s15 ← lift (Array.to_slice a15)
              let (r15, out16) ← fields out15 s15
              let cf15 ←
                core.result.Result.Insts.CoreOpsTry.branch
                  r15
              match cf15 with
              | core.ops.control_flow.ControlFlow.Continue _
                =>
                let a16 ← Array.index_usize values 16#usize
                let s16 ← lift (Array.to_slice a16)
                let (r16, out17) ← fields out16 s16
                let cf16 ←
                  core.result.Result.Insts.CoreOpsTry.branch
                    r16
                match cf16 with
                | core.ops.control_flow.ControlFlow.Continue
                  _ =>
                  let a17 ←
                    Array.index_usize values 17#usize
                  let s17 ← lift (Array.to_slice a17)
                  let (r17, out18) ← fields out17 s17
                  let cf17 ←
                    core.result.Result.Insts.CoreOpsTry.branch
                      r17
                  match cf17 with
                  |
                    core.ops.control_flow.ControlFlow.Continue
                    _ =>
                    let a18 ←
                      Array.index_usize values 18#usize
                    let s18 ← lift (Array.to_slice a18)
                    let (r18, out19) ← fields out18 s18
                    let cf18 ←
                      core.result.Result.Insts.CoreOpsTry.branch
                        r18
                    match cf18 with
                    |
                      core.ops.control_flow.ControlFlow.Continue
                      _ =>
                      let a19 ←
                        Array.index_usize values 19#usize
                      let s19 ← lift (Array.to_slice a19)
                      let (r19, out20) ← fields out19 s19
                      let cf19 ←
                        core.result.Result.Insts.CoreOpsTry.branch
                          r19
                      match cf19 with
                      |
                        core.ops.control_flow.ControlFlow.Continue
                        _ =>
                        ok (core.result.Result.Ok (), out20)
                      |
                        core.ops.control_flow.ControlFlow.Break
                        residual =>
                        let r20 ←
                          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                            Unit (core.convert.FromSame
                            aspis_core.state_only_prefix.r0.Error)
                            residual
                        ok (r20, out20)
                    | core.ops.control_flow.ControlFlow.Break
                      residual =>
                      let r19 ←
                        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                          Unit (core.convert.FromSame
                          aspis_core.state_only_prefix.r0.Error)
                          residual
                      ok (r19, out19)
                  | core.ops.control_flow.ControlFlow.Break
                    residual =>
                    let r18 ←
                      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                        Unit (core.convert.FromSame
                        aspis_core.state_only_prefix.r0.Error)
                        residual
                    ok (r18, out18)
                | core.ops.control_flow.ControlFlow.Break
                  residual =>
                  let r17 ←
                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                      Unit (core.convert.FromSame
                      aspis_core.state_only_prefix.r0.Error)
                      residual
                  ok (r17, out17)
              | core.ops.control_flow.ControlFlow.Break
                residual =>
                let r16 ←
                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                    Unit (core.convert.FromSame
                    aspis_core.state_only_prefix.r0.Error)
                    residual
                ok (r16, out16)
            | core.ops.control_flow.ControlFlow.Break
              residual =>
              let r15 ←
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                  Unit (core.convert.FromSame
                  aspis_core.state_only_prefix.r0.Error)
                  residual
              ok (r15, out15)
          | core.ops.control_flow.ControlFlow.Break residual
            =>
            let r14 ←
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                Unit (core.convert.FromSame
                aspis_core.state_only_prefix.r0.Error)
                residual
            ok (r14, out14)
        | core.ops.control_flow.ControlFlow.Break residual =>
          let r13 ←
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              Unit (core.convert.FromSame
              aspis_core.state_only_prefix.r0.Error) residual
          ok (r13, out13)
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r12 ←
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            Unit (core.convert.FromSame
            aspis_core.state_only_prefix.r0.Error) residual
        ok (r12, out12)
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r11 ←
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          Unit (core.convert.FromSame
          aspis_core.state_only_prefix.r0.Error) residual
      ok (r11, out11)
  | core.ops.control_flow.ControlFlow.Break residual =>
    let r10 ←
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        Unit (core.convert.FromSame
        aspis_core.state_only_prefix.r0.Error) residual
    ok (r10, out10)
theorem factor9_14 (fields : FF14) (out : alloc.vec.Vec U8) (values : FV14) :
    suffix9_14 fields out values = frontier_step14 fields (suffix10_14 fields) 9#usize out values := by
  unfold suffix9_14 frontier_step14 suffix10_14
  rfl
#print axioms factor9_14
end PV_B3P_FrontierStages14227
