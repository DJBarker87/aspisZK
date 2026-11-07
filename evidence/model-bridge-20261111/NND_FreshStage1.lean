import AdapterRwModel
set_option autoImplicit false
noncomputable section
namespace NND_FreshStage1
open Aeneas Aeneas.Std Result ControlFlow Error AdapterRw
def fresh (ops : Ops)
  (program_id : solana_pubkey.Pubkey)
  (accounts : Slice r1_pool_adapter.owned.OwnedAccount) (data : Slice Std.U8) :
  Result (core.result.Result (alloc.vec.Vec Std.U8)
    solana_program_error.ProgramError)
  := do
  let b ←
    ops.op1 core.cmp.PartialEqU8 data
      (Array.make 2#usize [ 3#u8, 10#u8 ])
  if b
  then
    let i := Slice.len accounts
    if i != 3#usize
    then
      ok (core.result.Result.Err
        solana_program_error.ProgramError.InvalidInstructionData)
    else
      let proof_account ← Slice.index_usize accounts 0#usize
      let public_account ← Slice.index_usize accounts 1#usize
      let checkpoint_account ← Slice.index_usize accounts 2#usize
      let r ←
        (r1_pool_adapter.owned.require_distinct_accounts ops)
          (Array.make 3#usize [
            proof_account, public_account, checkpoint_account
            ])
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r
      match cf with
      | core.ops.control_flow.ControlFlow.Continue _ =>
        let r1 ← r1_pool_adapter.owned.require_readonly_buffer proof_account
        let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
        match cf1 with
        | core.ops.control_flow.ControlFlow.Continue _ =>
          let r2 ←
            r1_pool_adapter.owned.require_readonly_buffer public_account
          let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
          match cf2 with
          | core.ops.control_flow.ControlFlow.Continue _ =>
            let r3 ←
              (r1_pool_adapter.owned.require_verifier_checkpoint ops)
                checkpoint_account program_id true
            let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r3
            match cf3 with
            | core.ops.control_flow.ControlFlow.Continue _ =>
              let r4 ←
                (r1_pool_adapter.owned.OwnedAccount.data ops) checkpoint_account
              let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r4
              match cf4 with
              | core.ops.control_flow.ControlFlow.Continue val =>
                let r5 ← r1_pool_adapter.owned.require_zero val
                let cf5 ← core.result.Result.Insts.CoreOpsTry.branch r5
                match cf5 with
                | core.ops.control_flow.ControlFlow.Continue _ =>
                  let r6 ←
                    (r1_pool_adapter.owned.OwnedAccount.data ops) public_account
                  let cf6 ← core.result.Result.Insts.CoreOpsTry.branch r6
                  match cf6 with
                  | core.ops.control_flow.ControlFlow.Continue val1 =>
                    let r7 ← ops.op47 val1
                    let cf7 ← core.result.Result.Insts.CoreOpsTry.branch r7
                    match cf7 with
                    | core.ops.control_flow.ControlFlow.Continue val2 =>
                      let r8 ←
                        ops.op21
                          val2
                      let r9 ←
                        core.result.Result.map_err
                          r1_pool_adapter.owned.stage1_owned.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestTerminalFormatErrorV1ProgramError
                          r8 ()
                      let cf8 ← core.result.Result.Insts.CoreOpsTry.branch r9
                      match cf8 with
                      | core.ops.control_flow.ControlFlow.Continue _ =>
                        let pvpftcv ←
                          aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.common
                            val2
                        let r10 ←
                          ops.op24
                            pvpftcv.lane_transition.candidate_afterstate
                        let r11 ←
                          core.result.Result.map_err
                            r1_pool_adapter.owned.stage1_owned.closure_1.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairVerifierTransportErrorV1ProgramError
                            r10 ()
                        let cf9 ←
                          core.result.Result.Insts.CoreOpsTry.branch r11
                        match cf9 with
                        | core.ops.control_flow.ControlFlow.Continue val3 =>
                          let r12 ←
                            (r1_pool_adapter.owned.OwnedAccount.data ops)
                              proof_account
                          let cf10 ←
                            core.result.Result.Insts.CoreOpsTry.branch r12
                          match cf10 with
                          | core.ops.control_flow.ControlFlow.Continue val4 =>
                            let proof_length ←
                              aspis_r1_cost_probe.verifier.PROOF_BYTES
                            let proof_start ←
                              (aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES ops)
                            let o ←
                              lift (Usize.checked_add proof_start proof_length)
                            let r13 ←
                              core.option.Option.ok_or o
                                solana_program_error.ProgramError.InvalidAccountData
                            let cf11 ←
                              core.result.Result.Insts.CoreOpsTry.branch r13
                            match cf11 with
                            | core.ops.control_flow.ControlFlow.Continue val5
                              =>
                              let i1 := Slice.len val4
                              if i1 != val5
                              then
                                ok (core.result.Result.Err
                                  solana_program_error.ProgramError.InvalidAccountData)
                              else
                                let s ←
                                  core.slice.index.Slice.index
                                    (core.slice.index.SliceIndexRangeToUsizeSlice
                                    Std.U8) val4 { «end» := proof_start }
                                let b1 ←
                                  ops.op0
                                    core.cmp.PartialEqU8 s val3
                                if b1
                                then
                                  ok (core.result.Result.Err
                                    solana_program_error.ProgramError.InvalidAccountData)
                                else
                                  let i2 ←
                                    lift (Std.Usize.wrapping_add proof_start
                                      8#usize)
                                  let i3 ← Slice.index_usize val4 i2
                                  let i4 ←
                                    aspis_r1_cost_probe.transport.Variant.tag
                                      aspis_r1_cost_probe.transport.Variant.S2
                                  if i3 != i4
                                  then
                                    ok (core.result.Result.Err
                                      solana_program_error.ProgramError.InvalidAccountData)
                                  else
                                    let p ←
                                      aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public
                                        val2
                                    let s1 ←
                                      core.slice.index.Slice.index
                                        (core.slice.index.SliceIndexRangeUsizeSlice
                                        Std.U8) val4
                                        { start := proof_start, «end» := val5
                                        }
                                    let i5 ← Slice.index_usize data 1#usize
                                    let i6 ← lift (UScalar.cast .Usize i5)
                                    let r14 ← (first_decoded ops) p val1 s1 i6
                                    let cf12 ←
                                      core.result.Result.Insts.CoreOpsTry.branch
                                        r14
                                    match cf12 with
                                    |
                                      core.ops.control_flow.ControlFlow.Continue
                                      val6 =>
                                      let i7 := alloc.vec.Vec.len val6
                                      let i8 := Slice.len val
                                      if i7 != i8
                                      then
                                        ok (core.result.Result.Err
                                          solana_program_error.ProgramError.InvalidAccountData)
                                      else ok (core.result.Result.Ok val6)
                                    | core.ops.control_flow.ControlFlow.Break
                                      residual =>
                                      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                        (alloc.vec.Vec Std.U8)
                                        (core.convert.FromSame
                                        solana_program_error.ProgramError)
                                        residual
                            | core.ops.control_flow.ControlFlow.Break residual
                              =>
                              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                (alloc.vec.Vec Std.U8) (core.convert.FromSame
                                solana_program_error.ProgramError) residual
                          | core.ops.control_flow.ControlFlow.Break residual =>
                            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                              (alloc.vec.Vec Std.U8) (core.convert.FromSame
                              solana_program_error.ProgramError) residual
                        | core.ops.control_flow.ControlFlow.Break residual =>
                          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                            (alloc.vec.Vec Std.U8) (core.convert.FromSame
                            solana_program_error.ProgramError) residual
                      | core.ops.control_flow.ControlFlow.Break residual =>
                        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                          (alloc.vec.Vec Std.U8) (core.convert.FromSame
                          solana_program_error.ProgramError) residual
                    | core.ops.control_flow.ControlFlow.Break residual =>
                      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                        (alloc.vec.Vec Std.U8) (core.convert.FromSame
                        solana_program_error.ProgramError) residual
                  | core.ops.control_flow.ControlFlow.Break residual =>
                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                      (alloc.vec.Vec Std.U8) (core.convert.FromSame
                      solana_program_error.ProgramError) residual
                | core.ops.control_flow.ControlFlow.Break residual =>
                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                    (alloc.vec.Vec Std.U8) (core.convert.FromSame
                    solana_program_error.ProgramError) residual
              | core.ops.control_flow.ControlFlow.Break residual =>
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                  (alloc.vec.Vec Std.U8) (core.convert.FromSame
                  solana_program_error.ProgramError) residual
            | core.ops.control_flow.ControlFlow.Break residual =>
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                (alloc.vec.Vec Std.U8) (core.convert.FromSame
                solana_program_error.ProgramError) residual
          | core.ops.control_flow.ControlFlow.Break residual =>
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              (alloc.vec.Vec Std.U8) (core.convert.FromSame
              solana_program_error.ProgramError) residual
        | core.ops.control_flow.ControlFlow.Break residual =>
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            (alloc.vec.Vec Std.U8) (core.convert.FromSame
            solana_program_error.ProgramError) residual
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          (alloc.vec.Vec Std.U8) (core.convert.FromSame
          solana_program_error.ProgramError) residual
  else
    let b1 ←
      ops.op1 core.cmp.PartialEqU8 data
        (Array.make 2#usize [ 3#u8, 11#u8 ])
    if b1
    then
      let i := Slice.len accounts
      if i != 3#usize
      then
        ok (core.result.Result.Err
          solana_program_error.ProgramError.InvalidInstructionData)
      else
        let proof_account ← Slice.index_usize accounts 0#usize
        let public_account ← Slice.index_usize accounts 1#usize
        let checkpoint_account ← Slice.index_usize accounts 2#usize
        let r ←
          (r1_pool_adapter.owned.require_distinct_accounts ops)
            (Array.make 3#usize [
              proof_account, public_account, checkpoint_account
              ])
        let cf ← core.result.Result.Insts.CoreOpsTry.branch r
        match cf with
        | core.ops.control_flow.ControlFlow.Continue _ =>
          let r1 ←
            r1_pool_adapter.owned.require_readonly_buffer proof_account
          let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
          match cf1 with
          | core.ops.control_flow.ControlFlow.Continue _ =>
            let r2 ←
              r1_pool_adapter.owned.require_readonly_buffer public_account
            let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
            match cf2 with
            | core.ops.control_flow.ControlFlow.Continue _ =>
              let r3 ←
                (r1_pool_adapter.owned.require_verifier_checkpoint ops)
                  checkpoint_account program_id true
              let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r3
              match cf3 with
              | core.ops.control_flow.ControlFlow.Continue _ =>
                let r4 ←
                  (r1_pool_adapter.owned.OwnedAccount.data ops) checkpoint_account
                let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r4
                match cf4 with
                | core.ops.control_flow.ControlFlow.Continue val =>
                  let r5 ← r1_pool_adapter.owned.require_zero val
                  let cf5 ← core.result.Result.Insts.CoreOpsTry.branch r5
                  match cf5 with
                  | core.ops.control_flow.ControlFlow.Continue _ =>
                    let r6 ←
                      (r1_pool_adapter.owned.OwnedAccount.data ops) public_account
                    let cf6 ← core.result.Result.Insts.CoreOpsTry.branch r6
                    match cf6 with
                    | core.ops.control_flow.ControlFlow.Continue val1 =>
                      let r7 ←
                        ops.op47 val1
                      let cf7 ← core.result.Result.Insts.CoreOpsTry.branch r7
                      match cf7 with
                      | core.ops.control_flow.ControlFlow.Continue val2 =>
                        let r8 ←
                          ops.op21
                            val2
                        let r9 ←
                          core.result.Result.map_err
                            r1_pool_adapter.owned.stage1_owned.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestTerminalFormatErrorV1ProgramError
                            r8 ()
                        let cf8 ←
                          core.result.Result.Insts.CoreOpsTry.branch r9
                        match cf8 with
                        | core.ops.control_flow.ControlFlow.Continue _ =>
                          let pvpftcv ←
                            aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.common
                              val2
                          let r10 ←
                            ops.op24
                              pvpftcv.lane_transition.candidate_afterstate
                          let r11 ←
                            core.result.Result.map_err
                              r1_pool_adapter.owned.stage1_owned.closure_1.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairVerifierTransportErrorV1ProgramError
                              r10 ()
                          let cf9 ←
                            core.result.Result.Insts.CoreOpsTry.branch r11
                          match cf9 with
                          | core.ops.control_flow.ControlFlow.Continue val3 =>
                            let r12 ←
                              (r1_pool_adapter.owned.OwnedAccount.data ops)
                                proof_account
                            let cf10 ←
                              core.result.Result.Insts.CoreOpsTry.branch r12
                            match cf10 with
                            | core.ops.control_flow.ControlFlow.Continue val4
                              =>
                              let proof_length ←
                                aspis_r1_cost_probe.verifier.PROOF_BYTES
                              let proof_start ←
                                (aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES ops)
                              let o ←
                                lift (Usize.checked_add proof_start
                                  proof_length)
                              let r13 ←
                                core.option.Option.ok_or o
                                  solana_program_error.ProgramError.InvalidAccountData
                              let cf11 ←
                                core.result.Result.Insts.CoreOpsTry.branch r13
                              match cf11 with
                              | core.ops.control_flow.ControlFlow.Continue val5
                                =>
                                let i1 := Slice.len val4
                                if i1 != val5
                                then
                                  ok (core.result.Result.Err
                                    solana_program_error.ProgramError.InvalidAccountData)
                                else
                                  let s ←
                                    core.slice.index.Slice.index
                                      (core.slice.index.SliceIndexRangeToUsizeSlice
                                      Std.U8) val4 { «end» := proof_start }
                                  let b2 ←
                                    ops.op0
                                      core.cmp.PartialEqU8 s val3
                                  if b2
                                  then
                                    ok (core.result.Result.Err
                                      solana_program_error.ProgramError.InvalidAccountData)
                                  else
                                    let i2 ←
                                      lift (Std.Usize.wrapping_add proof_start
                                        8#usize)
                                    let i3 ← Slice.index_usize val4 i2
                                    let i4 ←
                                      aspis_r1_cost_probe.transport.Variant.tag
                                        aspis_r1_cost_probe.transport.Variant.S2
                                    if i3 != i4
                                    then
                                      ok (core.result.Result.Err
                                        solana_program_error.ProgramError.InvalidAccountData)
                                    else
                                      let p ←
                                        aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public
                                          val2
                                      let s1 ←
                                        core.slice.index.Slice.index
                                          (core.slice.index.SliceIndexRangeUsizeSlice
                                          Std.U8) val4
                                          {
                                            start := proof_start,
                                            «end» := val5
                                          }
                                      let i5 ← Slice.index_usize data 1#usize
                                      let i6 ← lift (UScalar.cast .Usize i5)
                                      let r14 ← (first_decoded ops) p val1 s1 i6
                                      let cf12 ←
                                        core.result.Result.Insts.CoreOpsTry.branch
                                          r14
                                      match cf12 with
                                      |
                                        core.ops.control_flow.ControlFlow.Continue
                                        val6 =>
                                        let i7 := alloc.vec.Vec.len val6
                                        let i8 := Slice.len val
                                        if i7 != i8
                                        then
                                          ok (core.result.Result.Err
                                            solana_program_error.ProgramError.InvalidAccountData)
                                        else ok (core.result.Result.Ok val6)
                                      | core.ops.control_flow.ControlFlow.Break
                                        residual =>
                                        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                          (alloc.vec.Vec Std.U8)
                                          (core.convert.FromSame
                                          solana_program_error.ProgramError)
                                          residual
                              | core.ops.control_flow.ControlFlow.Break
                                residual =>
                                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                  (alloc.vec.Vec Std.U8) (core.convert.FromSame
                                  solana_program_error.ProgramError) residual
                            | core.ops.control_flow.ControlFlow.Break residual
                              =>
                              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                (alloc.vec.Vec Std.U8) (core.convert.FromSame
                                solana_program_error.ProgramError) residual
                          | core.ops.control_flow.ControlFlow.Break residual =>
                            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                              (alloc.vec.Vec Std.U8) (core.convert.FromSame
                              solana_program_error.ProgramError) residual
                        | core.ops.control_flow.ControlFlow.Break residual =>
                          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                            (alloc.vec.Vec Std.U8) (core.convert.FromSame
                            solana_program_error.ProgramError) residual
                      | core.ops.control_flow.ControlFlow.Break residual =>
                        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                          (alloc.vec.Vec Std.U8) (core.convert.FromSame
                          solana_program_error.ProgramError) residual
                    | core.ops.control_flow.ControlFlow.Break residual =>
                      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                        (alloc.vec.Vec Std.U8) (core.convert.FromSame
                        solana_program_error.ProgramError) residual
                  | core.ops.control_flow.ControlFlow.Break residual =>
                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                      (alloc.vec.Vec Std.U8) (core.convert.FromSame
                      solana_program_error.ProgramError) residual
                | core.ops.control_flow.ControlFlow.Break residual =>
                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                    (alloc.vec.Vec Std.U8) (core.convert.FromSame
                    solana_program_error.ProgramError) residual
              | core.ops.control_flow.ControlFlow.Break residual =>
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                  (alloc.vec.Vec Std.U8) (core.convert.FromSame
                  solana_program_error.ProgramError) residual
            | core.ops.control_flow.ControlFlow.Break residual =>
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                (alloc.vec.Vec Std.U8) (core.convert.FromSame
                solana_program_error.ProgramError) residual
          | core.ops.control_flow.ControlFlow.Break residual =>
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              (alloc.vec.Vec Std.U8) (core.convert.FromSame
              solana_program_error.ProgramError) residual
        | core.ops.control_flow.ControlFlow.Break residual =>
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            (alloc.vec.Vec Std.U8) (core.convert.FromSame
            solana_program_error.ProgramError) residual
    else
      ok (core.result.Result.Err
        solana_program_error.ProgramError.InvalidInstructionData)

/-- Parent body only: the opaque frozen require_zero boundary still needs
its own native/symbolic transport; it is not discharged by this equality. -/
theorem source (ops : Ops) (p : solana_pubkey.Pubkey)
 (a : Slice r1_pool_adapter.owned.OwnedAccount) (d : Slice U8) :
 fresh ops p a d = r1_pool_adapter.owned.stage1_owned ops p a d := rfl
#print axioms source
end NND_FreshStage1
end
