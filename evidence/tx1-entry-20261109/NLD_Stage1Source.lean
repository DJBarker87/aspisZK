import NLD_TraceControl
import NGL_FirstDecoded
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLD_Stage1Source
open Aeneas Aeneas.Std Result NLD_SourceTrace
open _root_.AdapterRw
/-- Complete canonical emitted stage1_owned, instrumented at every monadic
occurrence. This is a SOURCE trace; no native cut or SDK law is asserted. -/
def stage1Owned (ops : Ops)
  (program_id : solana_pubkey.Pubkey)
  (accounts : Slice r1_pool_adapter.owned.OwnedAccount) (data : Slice Std.U8) :
  Trace (core.result.Result (alloc.vec.Vec Std.U8)
    solana_program_error.ProgramError)
  := do
  let b ← call 2863 (
    ops.op1 core.cmp.PartialEqU8 data
      (Array.make 2#usize [ 3#u8, 10#u8 ])
  )
  if b
  then
    let i := Slice.len accounts
    if i != 3#usize
    then
      pure (core.result.Result.Err
        solana_program_error.ProgramError.InvalidInstructionData)
    else
      let proof_account ← call 2874 (
        Slice.index_usize accounts 0#usize
      )
      let public_account ← call 2875 (
        Slice.index_usize accounts 1#usize
      )
      let checkpoint_account ← call 2876 (
        Slice.index_usize accounts 2#usize
      )
      let r ← call 2877 (
        (r1_pool_adapter.owned.require_distinct_accounts ops)
          (Array.make 3#usize [
            proof_account, public_account, checkpoint_account
            ])
      )
      let cf ← call 2882 (
        core.result.Result.Insts.CoreOpsTry.branch r
      )
      match cf with
      | core.ops.control_flow.ControlFlow.Continue _ =>
        let r1 ← call 2885 (
          r1_pool_adapter.owned.require_readonly_buffer proof_account
        )
        let cf1 ← call 2886 (
          core.result.Result.Insts.CoreOpsTry.branch r1
        )
        match cf1 with
        | core.ops.control_flow.ControlFlow.Continue _ =>
          let r2 ← call 2889 (
            r1_pool_adapter.owned.require_readonly_buffer public_account
          )
          let cf2 ← call 2891 (
            core.result.Result.Insts.CoreOpsTry.branch r2
          )
          match cf2 with
          | core.ops.control_flow.ControlFlow.Continue _ =>
            let r3 ← call 2894 (
              (r1_pool_adapter.owned.require_verifier_checkpoint ops)
                checkpoint_account program_id true
            )
            let cf3 ← call 2897 (
              core.result.Result.Insts.CoreOpsTry.branch r3
            )
            match cf3 with
            | core.ops.control_flow.ControlFlow.Continue _ =>
              let r4 ← call 2900 (
                (r1_pool_adapter.owned.OwnedAccount.data ops) checkpoint_account
              )
              let cf4 ← call 2902 (
                core.result.Result.Insts.CoreOpsTry.branch r4
              )
              match cf4 with
              | core.ops.control_flow.ControlFlow.Continue val =>
                let r5 ← call 2905 (
                  r1_pool_adapter.owned.require_zero val
                )
                let cf5 ← call 2906 (
                  core.result.Result.Insts.CoreOpsTry.branch r5
                )
                match cf5 with
                | core.ops.control_flow.ControlFlow.Continue _ =>
                  let r6 ← call 2909 (
                    (r1_pool_adapter.owned.OwnedAccount.data ops) public_account
                  )
                  let cf6 ← call 2911 (
                    core.result.Result.Insts.CoreOpsTry.branch r6
                  )
                  match cf6 with
                  | core.ops.control_flow.ControlFlow.Continue val1 =>
                    let r7 ← call 2914 (
                      ops.op47 val1
                    )
                    let cf7 ← call 2915 (
                      core.result.Result.Insts.CoreOpsTry.branch r7
                    )
                    match cf7 with
                    | core.ops.control_flow.ControlFlow.Continue val2 =>
                      let r8 ← call 2918 (
                        ops.op21
                          val2
                      )
                      let r9 ← call 2921 (
                        core.result.Result.map_err
                          r1_pool_adapter.owned.stage1_owned.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestTerminalFormatErrorV1ProgramError
                          r8 ()
                      )
                      let cf8 ← call 2925 (
                        core.result.Result.Insts.CoreOpsTry.branch r9
                      )
                      match cf8 with
                      | core.ops.control_flow.ControlFlow.Continue _ =>
                        let pvpftcv ← call 2928 (
                          aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.common
                            val2
                        )
                        let r10 ← call 2931 (
                          ops.op24
                            pvpftcv.lane_transition.candidate_afterstate
                        )
                        let r11 ← call 2934 (
                          core.result.Result.map_err
                            r1_pool_adapter.owned.stage1_owned.closure_1.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairVerifierTransportErrorV1ProgramError
                            r10 ()
                        )
                        let cf9 ← call 2938 (
                          core.result.Result.Insts.CoreOpsTry.branch r11
                        )
                        match cf9 with
                        | core.ops.control_flow.ControlFlow.Continue val3 =>
                          let r12 ← call 2942 (
                            (r1_pool_adapter.owned.OwnedAccount.data ops)
                              proof_account
                          )
                          let cf10 ← call 2945 (
                            core.result.Result.Insts.CoreOpsTry.branch r12
                          )
                          match cf10 with
                          | core.ops.control_flow.ControlFlow.Continue val4 =>
                            let proof_length ← call 2949 (
                              aspis_r1_cost_probe.verifier.PROOF_BYTES
                            )
                            let proof_start ← call 2951 (
                              (aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES ops)
                            )
                            let o ← call 2953 (
                              lift (Usize.checked_add proof_start proof_length)
                            )
                            let r13 ← call 2955 (
                              core.option.Option.ok_or o
                                solana_program_error.ProgramError.InvalidAccountData
                            )
                            let cf11 ← call 2958 (
                              core.result.Result.Insts.CoreOpsTry.branch r13
                            )
                            match cf11 with
                            | core.ops.control_flow.ControlFlow.Continue val5
                              =>
                              let i1 := Slice.len val4
                              if i1 != val5
                              then
                                pure (core.result.Result.Err
                                  solana_program_error.ProgramError.InvalidAccountData)
                              else
                                let s ← call 2969 (
                                  core.slice.index.Slice.index
                                    (core.slice.index.SliceIndexRangeToUsizeSlice
                                    Std.U8) val4 { «end» := proof_start }
                                )
                                let b1 ← call 2973 (
                                  ops.op0
                                    core.cmp.PartialEqU8 s val3
                                )
                                if b1
                                then
                                  pure (core.result.Result.Err
                                    solana_program_error.ProgramError.InvalidAccountData)
                                else
                                  let i2 ← call 2981 (
                                    lift (Std.Usize.wrapping_add proof_start
                                      8#usize)
                                  )
                                  let i3 ← call 2984 (
                                    Slice.index_usize val4 i2
                                  )
                                  let i4 ← call 2985 (
                                    aspis_r1_cost_probe.transport.Variant.tag
                                      aspis_r1_cost_probe.transport.Variant.S2
                                  )
                                  if i3 != i4
                                  then
                                    pure (core.result.Result.Err
                                      solana_program_error.ProgramError.InvalidAccountData)
                                  else
                                    let p ← call 2993 (
                                      aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public
                                        val2
                                    )
                                    let s1 ← call 2996 (
                                      core.slice.index.Slice.index
                                        (core.slice.index.SliceIndexRangeUsizeSlice
                                        Std.U8) val4
                                        { start := proof_start, «end» := val5
                                        }
                                    )
                                    let i5 ← call 3002 (
                                      Slice.index_usize data 1#usize
                                    )
                                    let i6 ← call 3003 (
                                      lift (UScalar.cast .Usize i5)
                                    )
                                    let r14 ← call 3004 (
                                      (first_decoded ops) p val1 s1 i6
                                    )
                                    let cf12 ← call 3005 (
                                      core.result.Result.Insts.CoreOpsTry.branch
                                        r14
                                    )
                                    match cf12 with
                                    |
                                      core.ops.control_flow.ControlFlow.Continue
                                      val6 =>
                                      let i7 := alloc.vec.Vec.len val6
                                      let i8 := Slice.len val
                                      if i7 != i8
                                      then
                                        pure (core.result.Result.Err
                                          solana_program_error.ProgramError.InvalidAccountData)
                                      else pure (core.result.Result.Ok val6)
                                    | core.ops.control_flow.ControlFlow.Break
                                      residual =>
                                      call 3021 (
                                        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                        (alloc.vec.Vec Std.U8)
                                        (core.convert.FromSame
                                        solana_program_error.ProgramError)
                                        residual
                                      )
                            | core.ops.control_flow.ControlFlow.Break residual
                              =>
                              call 3028 (
                                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                (alloc.vec.Vec Std.U8) (core.convert.FromSame
                                solana_program_error.ProgramError) residual
                              )
                          | core.ops.control_flow.ControlFlow.Break residual =>
                            call 3032 (
                              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                              (alloc.vec.Vec Std.U8) (core.convert.FromSame
                              solana_program_error.ProgramError) residual
                            )
                        | core.ops.control_flow.ControlFlow.Break residual =>
                          call 3036 (
                            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                            (alloc.vec.Vec Std.U8) (core.convert.FromSame
                            solana_program_error.ProgramError) residual
                          )
                      | core.ops.control_flow.ControlFlow.Break residual =>
                        call 3040 (
                          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                          (alloc.vec.Vec Std.U8) (core.convert.FromSame
                          solana_program_error.ProgramError) residual
                        )
                    | core.ops.control_flow.ControlFlow.Break residual =>
                      call 3044 (
                        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                        (alloc.vec.Vec Std.U8) (core.convert.FromSame
                        solana_program_error.ProgramError) residual
                      )
                  | core.ops.control_flow.ControlFlow.Break residual =>
                    call 3048 (
                      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                      (alloc.vec.Vec Std.U8) (core.convert.FromSame
                      solana_program_error.ProgramError) residual
                    )
                | core.ops.control_flow.ControlFlow.Break residual =>
                  call 3052 (
                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                    (alloc.vec.Vec Std.U8) (core.convert.FromSame
                    solana_program_error.ProgramError) residual
                  )
              | core.ops.control_flow.ControlFlow.Break residual =>
                call 3056 (
                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                  (alloc.vec.Vec Std.U8) (core.convert.FromSame
                  solana_program_error.ProgramError) residual
                )
            | core.ops.control_flow.ControlFlow.Break residual =>
              call 3060 (
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                (alloc.vec.Vec Std.U8) (core.convert.FromSame
                solana_program_error.ProgramError) residual
              )
          | core.ops.control_flow.ControlFlow.Break residual =>
            call 3064 (
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              (alloc.vec.Vec Std.U8) (core.convert.FromSame
              solana_program_error.ProgramError) residual
            )
        | core.ops.control_flow.ControlFlow.Break residual =>
          call 3068 (
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            (alloc.vec.Vec Std.U8) (core.convert.FromSame
            solana_program_error.ProgramError) residual
          )
      | core.ops.control_flow.ControlFlow.Break residual =>
        call 3072 (
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          (alloc.vec.Vec Std.U8) (core.convert.FromSame
          solana_program_error.ProgramError) residual
        )
  else
    let b1 ← call 3076 (
      ops.op1 core.cmp.PartialEqU8 data
        (Array.make 2#usize [ 3#u8, 11#u8 ])
    )
    if b1
    then
      let i := Slice.len accounts
      if i != 3#usize
      then
        pure (core.result.Result.Err
          solana_program_error.ProgramError.InvalidInstructionData)
      else
        let proof_account ← call 3087 (
          Slice.index_usize accounts 0#usize
        )
        let public_account ← call 3088 (
          Slice.index_usize accounts 1#usize
        )
        let checkpoint_account ← call 3089 (
          Slice.index_usize accounts 2#usize
        )
        let r ← call 3090 (
          (r1_pool_adapter.owned.require_distinct_accounts ops)
            (Array.make 3#usize [
              proof_account, public_account, checkpoint_account
              ])
        )
        let cf ← call 3095 (
          core.result.Result.Insts.CoreOpsTry.branch r
        )
        match cf with
        | core.ops.control_flow.ControlFlow.Continue _ =>
          let r1 ← call 3098 (
            r1_pool_adapter.owned.require_readonly_buffer proof_account
          )
          let cf1 ← call 3100 (
            core.result.Result.Insts.CoreOpsTry.branch r1
          )
          match cf1 with
          | core.ops.control_flow.ControlFlow.Continue _ =>
            let r2 ← call 3103 (
              r1_pool_adapter.owned.require_readonly_buffer public_account
            )
            let cf2 ← call 3105 (
              core.result.Result.Insts.CoreOpsTry.branch r2
            )
            match cf2 with
            | core.ops.control_flow.ControlFlow.Continue _ =>
              let r3 ← call 3108 (
                (r1_pool_adapter.owned.require_verifier_checkpoint ops)
                  checkpoint_account program_id true
              )
              let cf3 ← call 3111 (
                core.result.Result.Insts.CoreOpsTry.branch r3
              )
              match cf3 with
              | core.ops.control_flow.ControlFlow.Continue _ =>
                let r4 ← call 3114 (
                  (r1_pool_adapter.owned.OwnedAccount.data ops) checkpoint_account
                )
                let cf4 ← call 3116 (
                  core.result.Result.Insts.CoreOpsTry.branch r4
                )
                match cf4 with
                | core.ops.control_flow.ControlFlow.Continue val =>
                  let r5 ← call 3119 (
                    r1_pool_adapter.owned.require_zero val
                  )
                  let cf5 ← call 3120 (
                    core.result.Result.Insts.CoreOpsTry.branch r5
                  )
                  match cf5 with
                  | core.ops.control_flow.ControlFlow.Continue _ =>
                    let r6 ← call 3123 (
                      (r1_pool_adapter.owned.OwnedAccount.data ops) public_account
                    )
                    let cf6 ← call 3125 (
                      core.result.Result.Insts.CoreOpsTry.branch r6
                    )
                    match cf6 with
                    | core.ops.control_flow.ControlFlow.Continue val1 =>
                      let r7 ← call 3128 (
                        ops.op47 val1
                      )
                      let cf7 ← call 3130 (
                        core.result.Result.Insts.CoreOpsTry.branch r7
                      )
                      match cf7 with
                      | core.ops.control_flow.ControlFlow.Continue val2 =>
                        let r8 ← call 3133 (
                          ops.op21
                            val2
                        )
                        let r9 ← call 3136 (
                          core.result.Result.map_err
                            r1_pool_adapter.owned.stage1_owned.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestTerminalFormatErrorV1ProgramError
                            r8 ()
                        )
                        let cf8 ← call 3140 (
                          core.result.Result.Insts.CoreOpsTry.branch r9
                        )
                        match cf8 with
                        | core.ops.control_flow.ControlFlow.Continue _ =>
                          let pvpftcv ← call 3144 (
                            aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.common
                              val2
                          )
                          let r10 ← call 3147 (
                            ops.op24
                              pvpftcv.lane_transition.candidate_afterstate
                          )
                          let r11 ← call 3150 (
                            core.result.Result.map_err
                              r1_pool_adapter.owned.stage1_owned.closure_1.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairVerifierTransportErrorV1ProgramError
                              r10 ()
                          )
                          let cf9 ← call 3154 (
                            core.result.Result.Insts.CoreOpsTry.branch r11
                          )
                          match cf9 with
                          | core.ops.control_flow.ControlFlow.Continue val3 =>
                            let r12 ← call 3158 (
                              (r1_pool_adapter.owned.OwnedAccount.data ops)
                                proof_account
                            )
                            let cf10 ← call 3161 (
                              core.result.Result.Insts.CoreOpsTry.branch r12
                            )
                            match cf10 with
                            | core.ops.control_flow.ControlFlow.Continue val4
                              =>
                              let proof_length ← call 3166 (
                                aspis_r1_cost_probe.verifier.PROOF_BYTES
                              )
                              let proof_start ← call 3168 (
                                (aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES ops)
                              )
                              let o ← call 3170 (
                                lift (Usize.checked_add proof_start
                                  proof_length)
                              )
                              let r13 ← call 3173 (
                                core.option.Option.ok_or o
                                  solana_program_error.ProgramError.InvalidAccountData
                              )
                              let cf11 ← call 3176 (
                                core.result.Result.Insts.CoreOpsTry.branch r13
                              )
                              match cf11 with
                              | core.ops.control_flow.ControlFlow.Continue val5
                                =>
                                let i1 := Slice.len val4
                                if i1 != val5
                                then
                                  pure (core.result.Result.Err
                                    solana_program_error.ProgramError.InvalidAccountData)
                                else
                                  let s ← call 3187 (
                                    core.slice.index.Slice.index
                                      (core.slice.index.SliceIndexRangeToUsizeSlice
                                      Std.U8) val4 { «end» := proof_start }
                                  )
                                  let b2 ← call 3191 (
                                    ops.op0
                                      core.cmp.PartialEqU8 s val3
                                  )
                                  if b2
                                  then
                                    pure (core.result.Result.Err
                                      solana_program_error.ProgramError.InvalidAccountData)
                                  else
                                    let i2 ← call 3199 (
                                      lift (Std.Usize.wrapping_add proof_start
                                        8#usize)
                                    )
                                    let i3 ← call 3202 (
                                      Slice.index_usize val4 i2
                                    )
                                    let i4 ← call 3203 (
                                      aspis_r1_cost_probe.transport.Variant.tag
                                        aspis_r1_cost_probe.transport.Variant.S2
                                    )
                                    if i3 != i4
                                    then
                                      pure (core.result.Result.Err
                                        solana_program_error.ProgramError.InvalidAccountData)
                                    else
                                      let p ← call 3211 (
                                        aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public
                                          val2
                                      )
                                      let s1 ← call 3214 (
                                        core.slice.index.Slice.index
                                          (core.slice.index.SliceIndexRangeUsizeSlice
                                          Std.U8) val4
                                          {
                                            start := proof_start,
                                            «end» := val5
                                          }
                                      )
                                      let i5 ← call 3222 (
                                        Slice.index_usize data 1#usize
                                      )
                                      let i6 ← call 3223 (
                                        lift (UScalar.cast .Usize i5)
                                      )
                                      let r14 ← call 3224 (
                                        (first_decoded ops) p val1 s1 i6
                                      )
                                      let cf12 ← call 3225 (
                                        core.result.Result.Insts.CoreOpsTry.branch
                                          r14
                                      )
                                      match cf12 with
                                      |
                                        core.ops.control_flow.ControlFlow.Continue
                                        val6 =>
                                        let i7 := alloc.vec.Vec.len val6
                                        let i8 := Slice.len val
                                        if i7 != i8
                                        then
                                          pure (core.result.Result.Err
                                            solana_program_error.ProgramError.InvalidAccountData)
                                        else pure (core.result.Result.Ok val6)
                                      | core.ops.control_flow.ControlFlow.Break
                                        residual =>
                                        call 3241 (
                                          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                          (alloc.vec.Vec Std.U8)
                                          (core.convert.FromSame
                                          solana_program_error.ProgramError)
                                          residual
                                        )
                              | core.ops.control_flow.ControlFlow.Break
                                residual =>
                                call 3248 (
                                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                  (alloc.vec.Vec Std.U8) (core.convert.FromSame
                                  solana_program_error.ProgramError) residual
                                )
                            | core.ops.control_flow.ControlFlow.Break residual
                              =>
                              call 3253 (
                                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                (alloc.vec.Vec Std.U8) (core.convert.FromSame
                                solana_program_error.ProgramError) residual
                              )
                          | core.ops.control_flow.ControlFlow.Break residual =>
                            call 3257 (
                              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                              (alloc.vec.Vec Std.U8) (core.convert.FromSame
                              solana_program_error.ProgramError) residual
                            )
                        | core.ops.control_flow.ControlFlow.Break residual =>
                          call 3261 (
                            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                            (alloc.vec.Vec Std.U8) (core.convert.FromSame
                            solana_program_error.ProgramError) residual
                          )
                      | core.ops.control_flow.ControlFlow.Break residual =>
                        call 3265 (
                          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                          (alloc.vec.Vec Std.U8) (core.convert.FromSame
                          solana_program_error.ProgramError) residual
                        )
                    | core.ops.control_flow.ControlFlow.Break residual =>
                      call 3269 (
                        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                        (alloc.vec.Vec Std.U8) (core.convert.FromSame
                        solana_program_error.ProgramError) residual
                      )
                  | core.ops.control_flow.ControlFlow.Break residual =>
                    call 3273 (
                      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                      (alloc.vec.Vec Std.U8) (core.convert.FromSame
                      solana_program_error.ProgramError) residual
                    )
                | core.ops.control_flow.ControlFlow.Break residual =>
                  call 3277 (
                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                    (alloc.vec.Vec Std.U8) (core.convert.FromSame
                    solana_program_error.ProgramError) residual
                  )
              | core.ops.control_flow.ControlFlow.Break residual =>
                call 3281 (
                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                  (alloc.vec.Vec Std.U8) (core.convert.FromSame
                  solana_program_error.ProgramError) residual
                )
            | core.ops.control_flow.ControlFlow.Break residual =>
              call 3285 (
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                (alloc.vec.Vec Std.U8) (core.convert.FromSame
                solana_program_error.ProgramError) residual
              )
          | core.ops.control_flow.ControlFlow.Break residual =>
            call 3289 (
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              (alloc.vec.Vec Std.U8) (core.convert.FromSame
              solana_program_error.ProgramError) residual
            )
        | core.ops.control_flow.ControlFlow.Break residual =>
          call 3293 (
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            (alloc.vec.Vec Std.U8) (core.convert.FromSame
            solana_program_error.ProgramError) residual
          )
    else
      pure (core.result.Result.Err
        solana_program_error.ProgramError.InvalidInstructionData)

theorem erasure (ops : AdapterRw.Ops) (program : AdapterRw.solana_pubkey.Pubkey)
    (accounts : Slice AdapterRw.r1_pool_adapter.owned.OwnedAccount) (data : Slice U8) :
    (stage1Owned ops program accounts data).2 =
      AdapterRw.r1_pool_adapter.owned.stage1_owned ops program accounts data := by
  simp only [stage1Owned,AdapterRw.r1_pool_adapter.owned.stage1_owned,
    erase_bind,erase_call,erase_pure,erase_if,erase_control]
  all_goals repeat' first
    | (with_reducible rfl)
    | (fail_if_no_progress simp only [erase_bind,erase_call,erase_pure,erase_if,erase_control])
    | (apply AspisR1.NLD_SourceTrace.bind_congr; intro x)
    | split
#print axioms erasure
end AspisR1.NLD_Stage1Source
