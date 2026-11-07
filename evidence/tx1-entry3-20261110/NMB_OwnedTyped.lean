import NMB_TypedCongr
import NLD_Stage1Source
set_option autoImplicit false
noncomputable section
namespace NMB_OwnedTyped
open Aeneas Aeneas.Std Result NMB_TypedTrace NMB_TypedControl
open _root_.AdapterRw
/-- NLD's COMPLETE emitted source, with full nominal replies and live values.
Ops is explicit source configuration, not hidden in environment or a row root.
This is SOURCE instrumentation only; full native child packets remain open. -/
def stage1Owned (ops : Ops)
  (program_id : solana_pubkey.Pubkey)
  (accounts : Slice r1_pool_adapter.owned.OwnedAccount) (data : Slice Std.U8) :
  Run (core.result.Result (alloc.vec.Vec Std.U8)
    solana_program_error.ProgramError)
  := do
  let b ← call 2863 [("program_id",pack program_id),("accounts",pack accounts),("data",pack data)] (
    ops.op1 core.cmp.PartialEqU8 data
      (Array.make 2#usize [ 3#u8, 10#u8 ])
  )
  if b
  then
    let i := Slice.len accounts
    if i != 3#usize
    then
      NMB_TypedTrace.pure (core.result.Result.Err
        solana_program_error.ProgramError.InvalidInstructionData)
    else
      let proof_account ← call 2874 [("program_id",pack program_id),("accounts",pack accounts),("data",pack data),("b",pack b),("i",pack i)] (
        Slice.index_usize accounts 0#usize
      )
      let public_account ← call 2875 [("program_id",pack program_id),("accounts",pack accounts),("data",pack data),("b",pack b),("i",pack i),("proof_account",pack proof_account)] (
        Slice.index_usize accounts 1#usize
      )
      let checkpoint_account ← call 2876 [("program_id",pack program_id),("accounts",pack accounts),("data",pack data),("b",pack b),("i",pack i),("proof_account",pack proof_account),("public_account",pack public_account)] (
        Slice.index_usize accounts 2#usize
      )
      let r ← call 2877 [("program_id",pack program_id),("accounts",pack accounts),("data",pack data),("b",pack b),("i",pack i),("proof_account",pack proof_account),("public_account",pack public_account),("checkpoint_account",pack checkpoint_account)] (
        (r1_pool_adapter.owned.require_distinct_accounts ops)
          (Array.make 3#usize [
            proof_account, public_account, checkpoint_account
            ])
      )
      let cf ← call 2882 [("program_id",pack program_id),("accounts",pack accounts),("data",pack data),("b",pack b),("i",pack i),("proof_account",pack proof_account),("public_account",pack public_account),("checkpoint_account",pack checkpoint_account),("r",pack r)] (
        core.result.Result.Insts.CoreOpsTry.branch r
      )
      match cf with
      | core.ops.control_flow.ControlFlow.Continue _ =>
        let r1 ← call 2885 [("program_id",pack program_id),("accounts",pack accounts),("data",pack data),("b",pack b),("i",pack i),("proof_account",pack proof_account),("public_account",pack public_account),("checkpoint_account",pack checkpoint_account),("r",pack r),("cf",pack cf)] (
          r1_pool_adapter.owned.require_readonly_buffer proof_account
        )
        let cf1 ← call 2886 [("program_id",pack program_id),("accounts",pack accounts),("data",pack data),("b",pack b),("i",pack i),("proof_account",pack proof_account),("public_account",pack public_account),("checkpoint_account",pack checkpoint_account),("r",pack r),("cf",pack cf),("r1",pack r1)] (
          core.result.Result.Insts.CoreOpsTry.branch r1
        )
        match cf1 with
        | core.ops.control_flow.ControlFlow.Continue _ =>
          let r2 ← call 2889 [("program_id",pack program_id),("accounts",pack accounts),("data",pack data),("b",pack b),("i",pack i),("proof_account",pack proof_account),("public_account",pack public_account),("checkpoint_account",pack checkpoint_account),("r",pack r),("cf",pack cf),("r1",pack r1),("cf1",pack cf1)] (
            r1_pool_adapter.owned.require_readonly_buffer public_account
          )
          let cf2 ← call 2891 [("program_id",pack program_id),("accounts",pack accounts),("data",pack data),("b",pack b),("i",pack i),("proof_account",pack proof_account),("public_account",pack public_account),("checkpoint_account",pack checkpoint_account),("r",pack r),("cf",pack cf),("r1",pack r1),("cf1",pack cf1),("r2",pack r2)] (
            core.result.Result.Insts.CoreOpsTry.branch r2
          )
          match cf2 with
          | core.ops.control_flow.ControlFlow.Continue _ =>
            let r3 ← call 2894 [("program_id",pack program_id),("accounts",pack accounts),("data",pack data),("b",pack b),("i",pack i),("proof_account",pack proof_account),("public_account",pack public_account),("checkpoint_account",pack checkpoint_account),("r",pack r),("cf",pack cf),("r1",pack r1),("cf1",pack cf1),("r2",pack r2),("cf2",pack cf2)] (
              (r1_pool_adapter.owned.require_verifier_checkpoint ops)
                checkpoint_account program_id true
            )
            let cf3 ← call 2897 [("program_id",pack program_id),("accounts",pack accounts),("data",pack data),("b",pack b),("i",pack i),("proof_account",pack proof_account),("public_account",pack public_account),("checkpoint_account",pack checkpoint_account),("r",pack r),("cf",pack cf),("r1",pack r1),("cf1",pack cf1),("r2",pack r2),("cf2",pack cf2),("r3",pack r3)] (
              core.result.Result.Insts.CoreOpsTry.branch r3
            )
            match cf3 with
            | core.ops.control_flow.ControlFlow.Continue _ =>
              let r4 ← call 2900 [("program_id",pack program_id),("accounts",pack accounts),("data",pack data),("b",pack b),("i",pack i),("proof_account",pack proof_account),("public_account",pack public_account),("checkpoint_account",pack checkpoint_account),("r",pack r),("cf",pack cf),("r1",pack r1),("cf1",pack cf1),("r2",pack r2),("cf2",pack cf2),("r3",pack r3),("cf3",pack cf3)] (
                (r1_pool_adapter.owned.OwnedAccount.data ops) checkpoint_account
              )
              let cf4 ← call 2902 [("program_id",pack program_id),("accounts",pack accounts),("data",pack data),("b",pack b),("i",pack i),("proof_account",pack proof_account),("public_account",pack public_account),("checkpoint_account",pack checkpoint_account),("r",pack r),("cf",pack cf),("r1",pack r1),("cf1",pack cf1),("r2",pack r2),("cf2",pack cf2),("r3",pack r3),("cf3",pack cf3),("r4",pack r4)] (
                core.result.Result.Insts.CoreOpsTry.branch r4
              )
              match cf4 with
              | core.ops.control_flow.ControlFlow.Continue val =>
                let r5 ← call 2905 [("program_id",pack program_id),("accounts",pack accounts),("data",pack data),("b",pack b),("i",pack i),("proof_account",pack proof_account),("public_account",pack public_account),("checkpoint_account",pack checkpoint_account),("r",pack r),("cf",pack cf),("r1",pack r1),("cf1",pack cf1),("r2",pack r2),("cf2",pack cf2),("r3",pack r3),("cf3",pack cf3),("r4",pack r4),("cf4",pack cf4),("val",pack val)] (
                  r1_pool_adapter.owned.require_zero val
                )
                let cf5 ← call 2906 [("program_id",pack program_id),("accounts",pack accounts),("data",pack data),("b",pack b),("i",pack i),("proof_account",pack proof_account),("public_account",pack public_account),("checkpoint_account",pack checkpoint_account),("r",pack r),("cf",pack cf),("r1",pack r1),("cf1",pack cf1),("r2",pack r2),("cf2",pack cf2),("r3",pack r3),("cf3",pack cf3),("r4",pack r4),("cf4",pack cf4),("val",pack val),("r5",pack r5)] (
                  core.result.Result.Insts.CoreOpsTry.branch r5
                )
                match cf5 with
                | core.ops.control_flow.ControlFlow.Continue _ =>
                  let r6 ← call 2909 [("program_id",pack program_id),("accounts",pack accounts),("data",pack data),("b",pack b),("i",pack i),("proof_account",pack proof_account),("public_account",pack public_account),("checkpoint_account",pack checkpoint_account),("r",pack r),("cf",pack cf),("r1",pack r1),("cf1",pack cf1),("r2",pack r2),("cf2",pack cf2),("r3",pack r3),("cf3",pack cf3),("r4",pack r4),("cf4",pack cf4),("val",pack val),("r5",pack r5),("cf5",pack cf5)] (
                    (r1_pool_adapter.owned.OwnedAccount.data ops) public_account
                  )
                  let cf6 ← call 2911 [("program_id",pack program_id),("accounts",pack accounts),("data",pack data),("b",pack b),("i",pack i),("proof_account",pack proof_account),("public_account",pack public_account),("checkpoint_account",pack checkpoint_account),("r",pack r),("cf",pack cf),("r1",pack r1),("cf1",pack cf1),("r2",pack r2),("cf2",pack cf2),("r3",pack r3),("cf3",pack cf3),("r4",pack r4),("cf4",pack cf4),("val",pack val),("r5",pack r5),("cf5",pack cf5),("r6",pack r6)] (
                    core.result.Result.Insts.CoreOpsTry.branch r6
                  )
                  match cf6 with
                  | core.ops.control_flow.ControlFlow.Continue val1 =>
                    let r7 ← call 2914 [("program_id",pack program_id),("accounts",pack accounts),("data",pack data),("b",pack b),("i",pack i),("proof_account",pack proof_account),("public_account",pack public_account),("checkpoint_account",pack checkpoint_account),("r",pack r),("cf",pack cf),("r1",pack r1),("cf1",pack cf1),("r2",pack r2),("cf2",pack cf2),("r3",pack r3),("cf3",pack cf3),("r4",pack r4),("cf4",pack cf4),("val",pack val),("r5",pack r5),("cf5",pack cf5),("r6",pack r6),("cf6",pack cf6),("val1",pack val1)] (
                      ops.op47 val1
                    )
                    let cf7 ← call 2915 [("program_id",pack program_id),("accounts",pack accounts),("data",pack data),("b",pack b),("i",pack i),("proof_account",pack proof_account),("public_account",pack public_account),("checkpoint_account",pack checkpoint_account),("r",pack r),("cf",pack cf),("r1",pack r1),("cf1",pack cf1),("r2",pack r2),("cf2",pack cf2),("r3",pack r3),("cf3",pack cf3),("r4",pack r4),("cf4",pack cf4),("val",pack val),("r5",pack r5),("cf5",pack cf5),("r6",pack r6),("cf6",pack cf6),("val1",pack val1),("r7",pack r7)] (
                      core.result.Result.Insts.CoreOpsTry.branch r7
                    )
                    match cf7 with
                    | core.ops.control_flow.ControlFlow.Continue val2 =>
                      let r8 ← call 2918 [("program_id",pack program_id),("accounts",pack accounts),("data",pack data),("b",pack b),("i",pack i),("proof_account",pack proof_account),("public_account",pack public_account),("checkpoint_account",pack checkpoint_account),("r",pack r),("cf",pack cf),("r1",pack r1),("cf1",pack cf1),("r2",pack r2),("cf2",pack cf2),("r3",pack r3),("cf3",pack cf3),("r4",pack r4),("cf4",pack cf4),("val",pack val),("r5",pack r5),("cf5",pack cf5),("r6",pack r6),("cf6",pack cf6),("val1",pack val1),("r7",pack r7),("cf7",pack cf7),("val2",pack val2)] (
                        ops.op21
                          val2
                      )
                      let r9 ← call 2921 [("program_id",pack program_id),("accounts",pack accounts),("data",pack data),("b",pack b),("i",pack i),("proof_account",pack proof_account),("public_account",pack public_account),("checkpoint_account",pack checkpoint_account),("r",pack r),("cf",pack cf),("r1",pack r1),("cf1",pack cf1),("r2",pack r2),("cf2",pack cf2),("r3",pack r3),("cf3",pack cf3),("r4",pack r4),("cf4",pack cf4),("val",pack val),("r5",pack r5),("cf5",pack cf5),("r6",pack r6),("cf6",pack cf6),("val1",pack val1),("r7",pack r7),("cf7",pack cf7),("val2",pack val2),("r8",pack r8)] (
                        core.result.Result.map_err
                          r1_pool_adapter.owned.stage1_owned.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestTerminalFormatErrorV1ProgramError
                          r8 ()
                      )
                      let cf8 ← call 2925 [("program_id",pack program_id),("accounts",pack accounts),("data",pack data),("b",pack b),("i",pack i),("proof_account",pack proof_account),("public_account",pack public_account),("checkpoint_account",pack checkpoint_account),("r",pack r),("cf",pack cf),("r1",pack r1),("cf1",pack cf1),("r2",pack r2),("cf2",pack cf2),("r3",pack r3),("cf3",pack cf3),("r4",pack r4),("cf4",pack cf4),("val",pack val),("r5",pack r5),("cf5",pack cf5),("r6",pack r6),("cf6",pack cf6),("val1",pack val1),("r7",pack r7),("cf7",pack cf7),("val2",pack val2),("r8",pack r8),("r9",pack r9)] (
                        core.result.Result.Insts.CoreOpsTry.branch r9
                      )
                      match cf8 with
                      | core.ops.control_flow.ControlFlow.Continue _ =>
                        let pvpftcv ← call 2928 [("program_id",pack program_id),("accounts",pack accounts),("data",pack data),("b",pack b),("i",pack i),("proof_account",pack proof_account),("public_account",pack public_account),("checkpoint_account",pack checkpoint_account),("r",pack r),("cf",pack cf),("r1",pack r1),("cf1",pack cf1),("r2",pack r2),("cf2",pack cf2),("r3",pack r3),("cf3",pack cf3),("r4",pack r4),("cf4",pack cf4),("val",pack val),("r5",pack r5),("cf5",pack cf5),("r6",pack r6),("cf6",pack cf6),("val1",pack val1),("r7",pack r7),("cf7",pack cf7),("val2",pack val2),("r8",pack r8),("r9",pack r9),("cf8",pack cf8)] (
                          aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.common
                            val2
                        )
                        let r10 ← call 2931 [("program_id",pack program_id),("accounts",pack accounts),("data",pack data),("b",pack b),("i",pack i),("proof_account",pack proof_account),("public_account",pack public_account),("checkpoint_account",pack checkpoint_account),("r",pack r),("cf",pack cf),("r1",pack r1),("cf1",pack cf1),("r2",pack r2),("cf2",pack cf2),("r3",pack r3),("cf3",pack cf3),("r4",pack r4),("cf4",pack cf4),("val",pack val),("r5",pack r5),("cf5",pack cf5),("r6",pack r6),("cf6",pack cf6),("val1",pack val1),("r7",pack r7),("cf7",pack cf7),("val2",pack val2),("r8",pack r8),("r9",pack r9),("cf8",pack cf8),("pvpftcv",pack pvpftcv)] (
                          ops.op24
                            pvpftcv.lane_transition.candidate_afterstate
                        )
                        let r11 ← call 2934 [("program_id",pack program_id),("accounts",pack accounts),("data",pack data),("b",pack b),("i",pack i),("proof_account",pack proof_account),("public_account",pack public_account),("checkpoint_account",pack checkpoint_account),("r",pack r),("cf",pack cf),("r1",pack r1),("cf1",pack cf1),("r2",pack r2),("cf2",pack cf2),("r3",pack r3),("cf3",pack cf3),("r4",pack r4),("cf4",pack cf4),("val",pack val),("r5",pack r5),("cf5",pack cf5),("r6",pack r6),("cf6",pack cf6),("val1",pack val1),("r7",pack r7),("cf7",pack cf7),("val2",pack val2),("r8",pack r8),("r9",pack r9),("cf8",pack cf8),("pvpftcv",pack pvpftcv),("r10",pack r10)] (
                          core.result.Result.map_err
                            r1_pool_adapter.owned.stage1_owned.closure_1.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairVerifierTransportErrorV1ProgramError
                            r10 ()
                        )
                        let cf9 ← call 2938 [("program_id",pack program_id),("accounts",pack accounts),("data",pack data),("b",pack b),("i",pack i),("proof_account",pack proof_account),("public_account",pack public_account),("checkpoint_account",pack checkpoint_account),("r",pack r),("cf",pack cf),("r1",pack r1),("cf1",pack cf1),("r2",pack r2),("cf2",pack cf2),("r3",pack r3),("cf3",pack cf3),("r4",pack r4),("cf4",pack cf4),("val",pack val),("r5",pack r5),("cf5",pack cf5),("r6",pack r6),("cf6",pack cf6),("val1",pack val1),("r7",pack r7),("cf7",pack cf7),("val2",pack val2),("r8",pack r8),("r9",pack r9),("cf8",pack cf8),("pvpftcv",pack pvpftcv),("r10",pack r10),("r11",pack r11)] (
                          core.result.Result.Insts.CoreOpsTry.branch r11
                        )
                        match cf9 with
                        | core.ops.control_flow.ControlFlow.Continue val3 =>
                          let r12 ← call 2942 [("program_id",pack program_id),("accounts",pack accounts),("data",pack data),("b",pack b),("i",pack i),("proof_account",pack proof_account),("public_account",pack public_account),("checkpoint_account",pack checkpoint_account),("r",pack r),("cf",pack cf),("r1",pack r1),("cf1",pack cf1),("r2",pack r2),("cf2",pack cf2),("r3",pack r3),("cf3",pack cf3),("r4",pack r4),("cf4",pack cf4),("val",pack val),("r5",pack r5),("cf5",pack cf5),("r6",pack r6),("cf6",pack cf6),("val1",pack val1),("r7",pack r7),("cf7",pack cf7),("val2",pack val2),("r8",pack r8),("r9",pack r9),("cf8",pack cf8),("pvpftcv",pack pvpftcv),("r10",pack r10),("r11",pack r11),("cf9",pack cf9),("val3",pack val3)] (
                            (r1_pool_adapter.owned.OwnedAccount.data ops)
                              proof_account
                          )
                          let cf10 ← call 2945 [("program_id",pack program_id),("accounts",pack accounts),("data",pack data),("b",pack b),("i",pack i),("proof_account",pack proof_account),("public_account",pack public_account),("checkpoint_account",pack checkpoint_account),("r",pack r),("cf",pack cf),("r1",pack r1),("cf1",pack cf1),("r2",pack r2),("cf2",pack cf2),("r3",pack r3),("cf3",pack cf3),("r4",pack r4),("cf4",pack cf4),("val",pack val),("r5",pack r5),("cf5",pack cf5),("r6",pack r6),("cf6",pack cf6),("val1",pack val1),("r7",pack r7),("cf7",pack cf7),("val2",pack val2),("r8",pack r8),("r9",pack r9),("cf8",pack cf8),("pvpftcv",pack pvpftcv),("r10",pack r10),("r11",pack r11),("cf9",pack cf9),("val3",pack val3),("r12",pack r12)] (
                            core.result.Result.Insts.CoreOpsTry.branch r12
                          )
                          match cf10 with
                          | core.ops.control_flow.ControlFlow.Continue val4 =>
                            let proof_length ← call 2949 [("program_id",pack program_id),("accounts",pack accounts),("data",pack data),("b",pack b),("i",pack i),("proof_account",pack proof_account),("public_account",pack public_account),("checkpoint_account",pack checkpoint_account),("r",pack r),("cf",pack cf),("r1",pack r1),("cf1",pack cf1),("r2",pack r2),("cf2",pack cf2),("r3",pack r3),("cf3",pack cf3),("r4",pack r4),("cf4",pack cf4),("val",pack val),("r5",pack r5),("cf5",pack cf5),("r6",pack r6),("cf6",pack cf6),("val1",pack val1),("r7",pack r7),("cf7",pack cf7),("val2",pack val2),("r8",pack r8),("r9",pack r9),("cf8",pack cf8),("pvpftcv",pack pvpftcv),("r10",pack r10),("r11",pack r11),("cf9",pack cf9),("val3",pack val3),("r12",pack r12),("cf10",pack cf10),("val4",pack val4)] (
                              aspis_r1_cost_probe.verifier.PROOF_BYTES
                            )
                            let proof_start ← call 2951 [("program_id",pack program_id),("accounts",pack accounts),("data",pack data),("b",pack b),("i",pack i),("proof_account",pack proof_account),("public_account",pack public_account),("checkpoint_account",pack checkpoint_account),("r",pack r),("cf",pack cf),("r1",pack r1),("cf1",pack cf1),("r2",pack r2),("cf2",pack cf2),("r3",pack r3),("cf3",pack cf3),("r4",pack r4),("cf4",pack cf4),("val",pack val),("r5",pack r5),("cf5",pack cf5),("r6",pack r6),("cf6",pack cf6),("val1",pack val1),("r7",pack r7),("cf7",pack cf7),("val2",pack val2),("r8",pack r8),("r9",pack r9),("cf8",pack cf8),("pvpftcv",pack pvpftcv),("r10",pack r10),("r11",pack r11),("cf9",pack cf9),("val3",pack val3),("r12",pack r12),("cf10",pack cf10),("val4",pack val4),("proof_length",pack proof_length)] (
                              (aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES ops)
                            )
                            let o ← call 2953 [("program_id",pack program_id),("accounts",pack accounts),("data",pack data),("b",pack b),("i",pack i),("proof_account",pack proof_account),("public_account",pack public_account),("checkpoint_account",pack checkpoint_account),("r",pack r),("cf",pack cf),("r1",pack r1),("cf1",pack cf1),("r2",pack r2),("cf2",pack cf2),("r3",pack r3),("cf3",pack cf3),("r4",pack r4),("cf4",pack cf4),("val",pack val),("r5",pack r5),("cf5",pack cf5),("r6",pack r6),("cf6",pack cf6),("val1",pack val1),("r7",pack r7),("cf7",pack cf7),("val2",pack val2),("r8",pack r8),("r9",pack r9),("cf8",pack cf8),("pvpftcv",pack pvpftcv),("r10",pack r10),("r11",pack r11),("cf9",pack cf9),("val3",pack val3),("r12",pack r12),("cf10",pack cf10),("val4",pack val4),("proof_length",pack proof_length),("proof_start",pack proof_start)] (
                              lift (Usize.checked_add proof_start proof_length)
                            )
                            let r13 ← call 2955 [("program_id",pack program_id),("accounts",pack accounts),("data",pack data),("b",pack b),("i",pack i),("proof_account",pack proof_account),("public_account",pack public_account),("checkpoint_account",pack checkpoint_account),("r",pack r),("cf",pack cf),("r1",pack r1),("cf1",pack cf1),("r2",pack r2),("cf2",pack cf2),("r3",pack r3),("cf3",pack cf3),("r4",pack r4),("cf4",pack cf4),("val",pack val),("r5",pack r5),("cf5",pack cf5),("r6",pack r6),("cf6",pack cf6),("val1",pack val1),("r7",pack r7),("cf7",pack cf7),("val2",pack val2),("r8",pack r8),("r9",pack r9),("cf8",pack cf8),("pvpftcv",pack pvpftcv),("r10",pack r10),("r11",pack r11),("cf9",pack cf9),("val3",pack val3),("r12",pack r12),("cf10",pack cf10),("val4",pack val4),("proof_length",pack proof_length),("proof_start",pack proof_start),("o",pack o)] (
                              core.option.Option.ok_or o
                                solana_program_error.ProgramError.InvalidAccountData
                            )
                            let cf11 ← call 2958 [("program_id",pack program_id),("accounts",pack accounts),("data",pack data),("b",pack b),("i",pack i),("proof_account",pack proof_account),("public_account",pack public_account),("checkpoint_account",pack checkpoint_account),("r",pack r),("cf",pack cf),("r1",pack r1),("cf1",pack cf1),("r2",pack r2),("cf2",pack cf2),("r3",pack r3),("cf3",pack cf3),("r4",pack r4),("cf4",pack cf4),("val",pack val),("r5",pack r5),("cf5",pack cf5),("r6",pack r6),("cf6",pack cf6),("val1",pack val1),("r7",pack r7),("cf7",pack cf7),("val2",pack val2),("r8",pack r8),("r9",pack r9),("cf8",pack cf8),("pvpftcv",pack pvpftcv),("r10",pack r10),("r11",pack r11),("cf9",pack cf9),("val3",pack val3),("r12",pack r12),("cf10",pack cf10),("val4",pack val4),("proof_length",pack proof_length),("proof_start",pack proof_start),("o",pack o),("r13",pack r13)] (
                              core.result.Result.Insts.CoreOpsTry.branch r13
                            )
                            match cf11 with
                            | core.ops.control_flow.ControlFlow.Continue val5
                              =>
                              let i1 := Slice.len val4
                              if i1 != val5
                              then
                                NMB_TypedTrace.pure (core.result.Result.Err
                                  solana_program_error.ProgramError.InvalidAccountData)
                              else
                                let s ← call 2969 [("program_id",pack program_id),("accounts",pack accounts),("data",pack data),("b",pack b),("i",pack i),("proof_account",pack proof_account),("public_account",pack public_account),("checkpoint_account",pack checkpoint_account),("r",pack r),("cf",pack cf),("r1",pack r1),("cf1",pack cf1),("r2",pack r2),("cf2",pack cf2),("r3",pack r3),("cf3",pack cf3),("r4",pack r4),("cf4",pack cf4),("val",pack val),("r5",pack r5),("cf5",pack cf5),("r6",pack r6),("cf6",pack cf6),("val1",pack val1),("r7",pack r7),("cf7",pack cf7),("val2",pack val2),("r8",pack r8),("r9",pack r9),("cf8",pack cf8),("pvpftcv",pack pvpftcv),("r10",pack r10),("r11",pack r11),("cf9",pack cf9),("val3",pack val3),("r12",pack r12),("cf10",pack cf10),("val4",pack val4),("proof_length",pack proof_length),("proof_start",pack proof_start),("o",pack o),("r13",pack r13),("cf11",pack cf11),("val5",pack val5),("i1",pack i1)] (
                                  core.slice.index.Slice.index
                                    (core.slice.index.SliceIndexRangeToUsizeSlice
                                    Std.U8) val4 { «end» := proof_start }
                                )
                                let b1 ← call 2973 [("program_id",pack program_id),("accounts",pack accounts),("data",pack data),("b",pack b),("i",pack i),("proof_account",pack proof_account),("public_account",pack public_account),("checkpoint_account",pack checkpoint_account),("r",pack r),("cf",pack cf),("r1",pack r1),("cf1",pack cf1),("r2",pack r2),("cf2",pack cf2),("r3",pack r3),("cf3",pack cf3),("r4",pack r4),("cf4",pack cf4),("val",pack val),("r5",pack r5),("cf5",pack cf5),("r6",pack r6),("cf6",pack cf6),("val1",pack val1),("r7",pack r7),("cf7",pack cf7),("val2",pack val2),("r8",pack r8),("r9",pack r9),("cf8",pack cf8),("pvpftcv",pack pvpftcv),("r10",pack r10),("r11",pack r11),("cf9",pack cf9),("val3",pack val3),("r12",pack r12),("cf10",pack cf10),("val4",pack val4),("proof_length",pack proof_length),("proof_start",pack proof_start),("o",pack o),("r13",pack r13),("cf11",pack cf11),("val5",pack val5),("i1",pack i1),("s",pack s)] (
                                  ops.op0
                                    core.cmp.PartialEqU8 s val3
                                )
                                if b1
                                then
                                  NMB_TypedTrace.pure (core.result.Result.Err
                                    solana_program_error.ProgramError.InvalidAccountData)
                                else
                                  let i2 ← call 2981 [("program_id",pack program_id),("accounts",pack accounts),("data",pack data),("b",pack b),("i",pack i),("proof_account",pack proof_account),("public_account",pack public_account),("checkpoint_account",pack checkpoint_account),("r",pack r),("cf",pack cf),("r1",pack r1),("cf1",pack cf1),("r2",pack r2),("cf2",pack cf2),("r3",pack r3),("cf3",pack cf3),("r4",pack r4),("cf4",pack cf4),("val",pack val),("r5",pack r5),("cf5",pack cf5),("r6",pack r6),("cf6",pack cf6),("val1",pack val1),("r7",pack r7),("cf7",pack cf7),("val2",pack val2),("r8",pack r8),("r9",pack r9),("cf8",pack cf8),("pvpftcv",pack pvpftcv),("r10",pack r10),("r11",pack r11),("cf9",pack cf9),("val3",pack val3),("r12",pack r12),("cf10",pack cf10),("val4",pack val4),("proof_length",pack proof_length),("proof_start",pack proof_start),("o",pack o),("r13",pack r13),("cf11",pack cf11),("val5",pack val5),("i1",pack i1),("s",pack s),("b1",pack b1)] (
                                    lift (Std.Usize.wrapping_add proof_start
                                      8#usize)
                                  )
                                  let i3 ← call 2984 [("program_id",pack program_id),("accounts",pack accounts),("data",pack data),("b",pack b),("i",pack i),("proof_account",pack proof_account),("public_account",pack public_account),("checkpoint_account",pack checkpoint_account),("r",pack r),("cf",pack cf),("r1",pack r1),("cf1",pack cf1),("r2",pack r2),("cf2",pack cf2),("r3",pack r3),("cf3",pack cf3),("r4",pack r4),("cf4",pack cf4),("val",pack val),("r5",pack r5),("cf5",pack cf5),("r6",pack r6),("cf6",pack cf6),("val1",pack val1),("r7",pack r7),("cf7",pack cf7),("val2",pack val2),("r8",pack r8),("r9",pack r9),("cf8",pack cf8),("pvpftcv",pack pvpftcv),("r10",pack r10),("r11",pack r11),("cf9",pack cf9),("val3",pack val3),("r12",pack r12),("cf10",pack cf10),("val4",pack val4),("proof_length",pack proof_length),("proof_start",pack proof_start),("o",pack o),("r13",pack r13),("cf11",pack cf11),("val5",pack val5),("i1",pack i1),("s",pack s),("b1",pack b1),("i2",pack i2)] (
                                    Slice.index_usize val4 i2
                                  )
                                  let i4 ← call 2985 [("program_id",pack program_id),("accounts",pack accounts),("data",pack data),("b",pack b),("i",pack i),("proof_account",pack proof_account),("public_account",pack public_account),("checkpoint_account",pack checkpoint_account),("r",pack r),("cf",pack cf),("r1",pack r1),("cf1",pack cf1),("r2",pack r2),("cf2",pack cf2),("r3",pack r3),("cf3",pack cf3),("r4",pack r4),("cf4",pack cf4),("val",pack val),("r5",pack r5),("cf5",pack cf5),("r6",pack r6),("cf6",pack cf6),("val1",pack val1),("r7",pack r7),("cf7",pack cf7),("val2",pack val2),("r8",pack r8),("r9",pack r9),("cf8",pack cf8),("pvpftcv",pack pvpftcv),("r10",pack r10),("r11",pack r11),("cf9",pack cf9),("val3",pack val3),("r12",pack r12),("cf10",pack cf10),("val4",pack val4),("proof_length",pack proof_length),("proof_start",pack proof_start),("o",pack o),("r13",pack r13),("cf11",pack cf11),("val5",pack val5),("i1",pack i1),("s",pack s),("b1",pack b1),("i2",pack i2),("i3",pack i3)] (
                                    aspis_r1_cost_probe.transport.Variant.tag
                                      aspis_r1_cost_probe.transport.Variant.S2
                                  )
                                  if i3 != i4
                                  then
                                    NMB_TypedTrace.pure (core.result.Result.Err
                                      solana_program_error.ProgramError.InvalidAccountData)
                                  else
                                    let p ← call 2993 [("program_id",pack program_id),("accounts",pack accounts),("data",pack data),("b",pack b),("i",pack i),("proof_account",pack proof_account),("public_account",pack public_account),("checkpoint_account",pack checkpoint_account),("r",pack r),("cf",pack cf),("r1",pack r1),("cf1",pack cf1),("r2",pack r2),("cf2",pack cf2),("r3",pack r3),("cf3",pack cf3),("r4",pack r4),("cf4",pack cf4),("val",pack val),("r5",pack r5),("cf5",pack cf5),("r6",pack r6),("cf6",pack cf6),("val1",pack val1),("r7",pack r7),("cf7",pack cf7),("val2",pack val2),("r8",pack r8),("r9",pack r9),("cf8",pack cf8),("pvpftcv",pack pvpftcv),("r10",pack r10),("r11",pack r11),("cf9",pack cf9),("val3",pack val3),("r12",pack r12),("cf10",pack cf10),("val4",pack val4),("proof_length",pack proof_length),("proof_start",pack proof_start),("o",pack o),("r13",pack r13),("cf11",pack cf11),("val5",pack val5),("i1",pack i1),("s",pack s),("b1",pack b1),("i2",pack i2),("i3",pack i3),("i4",pack i4)] (
                                      aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public
                                        val2
                                    )
                                    let s1 ← call 2996 [("program_id",pack program_id),("accounts",pack accounts),("data",pack data),("b",pack b),("i",pack i),("proof_account",pack proof_account),("public_account",pack public_account),("checkpoint_account",pack checkpoint_account),("r",pack r),("cf",pack cf),("r1",pack r1),("cf1",pack cf1),("r2",pack r2),("cf2",pack cf2),("r3",pack r3),("cf3",pack cf3),("r4",pack r4),("cf4",pack cf4),("val",pack val),("r5",pack r5),("cf5",pack cf5),("r6",pack r6),("cf6",pack cf6),("val1",pack val1),("r7",pack r7),("cf7",pack cf7),("val2",pack val2),("r8",pack r8),("r9",pack r9),("cf8",pack cf8),("pvpftcv",pack pvpftcv),("r10",pack r10),("r11",pack r11),("cf9",pack cf9),("val3",pack val3),("r12",pack r12),("cf10",pack cf10),("val4",pack val4),("proof_length",pack proof_length),("proof_start",pack proof_start),("o",pack o),("r13",pack r13),("cf11",pack cf11),("val5",pack val5),("i1",pack i1),("s",pack s),("b1",pack b1),("i2",pack i2),("i3",pack i3),("i4",pack i4),("p",pack p)] (
                                      core.slice.index.Slice.index
                                        (core.slice.index.SliceIndexRangeUsizeSlice
                                        Std.U8) val4
                                        { start := proof_start, «end» := val5
                                        }
                                    )
                                    let i5 ← call 3002 [("program_id",pack program_id),("accounts",pack accounts),("data",pack data),("b",pack b),("i",pack i),("proof_account",pack proof_account),("public_account",pack public_account),("checkpoint_account",pack checkpoint_account),("r",pack r),("cf",pack cf),("r1",pack r1),("cf1",pack cf1),("r2",pack r2),("cf2",pack cf2),("r3",pack r3),("cf3",pack cf3),("r4",pack r4),("cf4",pack cf4),("val",pack val),("r5",pack r5),("cf5",pack cf5),("r6",pack r6),("cf6",pack cf6),("val1",pack val1),("r7",pack r7),("cf7",pack cf7),("val2",pack val2),("r8",pack r8),("r9",pack r9),("cf8",pack cf8),("pvpftcv",pack pvpftcv),("r10",pack r10),("r11",pack r11),("cf9",pack cf9),("val3",pack val3),("r12",pack r12),("cf10",pack cf10),("val4",pack val4),("proof_length",pack proof_length),("proof_start",pack proof_start),("o",pack o),("r13",pack r13),("cf11",pack cf11),("val5",pack val5),("i1",pack i1),("s",pack s),("b1",pack b1),("i2",pack i2),("i3",pack i3),("i4",pack i4),("p",pack p),("s1",pack s1)] (
                                      Slice.index_usize data 1#usize
                                    )
                                    let i6 ← call 3003 [("program_id",pack program_id),("accounts",pack accounts),("data",pack data),("b",pack b),("i",pack i),("proof_account",pack proof_account),("public_account",pack public_account),("checkpoint_account",pack checkpoint_account),("r",pack r),("cf",pack cf),("r1",pack r1),("cf1",pack cf1),("r2",pack r2),("cf2",pack cf2),("r3",pack r3),("cf3",pack cf3),("r4",pack r4),("cf4",pack cf4),("val",pack val),("r5",pack r5),("cf5",pack cf5),("r6",pack r6),("cf6",pack cf6),("val1",pack val1),("r7",pack r7),("cf7",pack cf7),("val2",pack val2),("r8",pack r8),("r9",pack r9),("cf8",pack cf8),("pvpftcv",pack pvpftcv),("r10",pack r10),("r11",pack r11),("cf9",pack cf9),("val3",pack val3),("r12",pack r12),("cf10",pack cf10),("val4",pack val4),("proof_length",pack proof_length),("proof_start",pack proof_start),("o",pack o),("r13",pack r13),("cf11",pack cf11),("val5",pack val5),("i1",pack i1),("s",pack s),("b1",pack b1),("i2",pack i2),("i3",pack i3),("i4",pack i4),("p",pack p),("s1",pack s1),("i5",pack i5)] (
                                      lift (UScalar.cast .Usize i5)
                                    )
                                    let r14 ← call 3004 [("program_id",pack program_id),("accounts",pack accounts),("data",pack data),("b",pack b),("i",pack i),("proof_account",pack proof_account),("public_account",pack public_account),("checkpoint_account",pack checkpoint_account),("r",pack r),("cf",pack cf),("r1",pack r1),("cf1",pack cf1),("r2",pack r2),("cf2",pack cf2),("r3",pack r3),("cf3",pack cf3),("r4",pack r4),("cf4",pack cf4),("val",pack val),("r5",pack r5),("cf5",pack cf5),("r6",pack r6),("cf6",pack cf6),("val1",pack val1),("r7",pack r7),("cf7",pack cf7),("val2",pack val2),("r8",pack r8),("r9",pack r9),("cf8",pack cf8),("pvpftcv",pack pvpftcv),("r10",pack r10),("r11",pack r11),("cf9",pack cf9),("val3",pack val3),("r12",pack r12),("cf10",pack cf10),("val4",pack val4),("proof_length",pack proof_length),("proof_start",pack proof_start),("o",pack o),("r13",pack r13),("cf11",pack cf11),("val5",pack val5),("i1",pack i1),("s",pack s),("b1",pack b1),("i2",pack i2),("i3",pack i3),("i4",pack i4),("p",pack p),("s1",pack s1),("i5",pack i5),("i6",pack i6)] (
                                      (first_decoded ops) p val1 s1 i6
                                    )
                                    let cf12 ← call 3005 [("program_id",pack program_id),("accounts",pack accounts),("data",pack data),("b",pack b),("i",pack i),("proof_account",pack proof_account),("public_account",pack public_account),("checkpoint_account",pack checkpoint_account),("r",pack r),("cf",pack cf),("r1",pack r1),("cf1",pack cf1),("r2",pack r2),("cf2",pack cf2),("r3",pack r3),("cf3",pack cf3),("r4",pack r4),("cf4",pack cf4),("val",pack val),("r5",pack r5),("cf5",pack cf5),("r6",pack r6),("cf6",pack cf6),("val1",pack val1),("r7",pack r7),("cf7",pack cf7),("val2",pack val2),("r8",pack r8),("r9",pack r9),("cf8",pack cf8),("pvpftcv",pack pvpftcv),("r10",pack r10),("r11",pack r11),("cf9",pack cf9),("val3",pack val3),("r12",pack r12),("cf10",pack cf10),("val4",pack val4),("proof_length",pack proof_length),("proof_start",pack proof_start),("o",pack o),("r13",pack r13),("cf11",pack cf11),("val5",pack val5),("i1",pack i1),("s",pack s),("b1",pack b1),("i2",pack i2),("i3",pack i3),("i4",pack i4),("p",pack p),("s1",pack s1),("i5",pack i5),("i6",pack i6),("r14",pack r14)] (
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
                                        NMB_TypedTrace.pure (core.result.Result.Err
                                          solana_program_error.ProgramError.InvalidAccountData)
                                      else NMB_TypedTrace.pure (core.result.Result.Ok val6)
                                    | core.ops.control_flow.ControlFlow.Break
                                      residual =>
                                      call 3021 [("program_id",pack program_id),("accounts",pack accounts),("data",pack data),("b",pack b),("i",pack i),("proof_account",pack proof_account),("public_account",pack public_account),("checkpoint_account",pack checkpoint_account),("r",pack r),("cf",pack cf),("r1",pack r1),("cf1",pack cf1),("r2",pack r2),("cf2",pack cf2),("r3",pack r3),("cf3",pack cf3),("r4",pack r4),("cf4",pack cf4),("val",pack val),("r5",pack r5),("cf5",pack cf5),("r6",pack r6),("cf6",pack cf6),("val1",pack val1),("r7",pack r7),("cf7",pack cf7),("val2",pack val2),("r8",pack r8),("r9",pack r9),("cf8",pack cf8),("pvpftcv",pack pvpftcv),("r10",pack r10),("r11",pack r11),("cf9",pack cf9),("val3",pack val3),("r12",pack r12),("cf10",pack cf10),("val4",pack val4),("proof_length",pack proof_length),("proof_start",pack proof_start),("o",pack o),("r13",pack r13),("cf11",pack cf11),("val5",pack val5),("i1",pack i1),("s",pack s),("b1",pack b1),("i2",pack i2),("i3",pack i3),("i4",pack i4),("p",pack p),("s1",pack s1),("i5",pack i5),("i6",pack i6),("r14",pack r14),("cf12",pack cf12)] (
                                        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                        (alloc.vec.Vec Std.U8)
                                        (core.convert.FromSame
                                        solana_program_error.ProgramError)
                                        residual
                                      )
                            | core.ops.control_flow.ControlFlow.Break residual
                              =>
                              call 3028 [("program_id",pack program_id),("accounts",pack accounts),("data",pack data),("b",pack b),("i",pack i),("proof_account",pack proof_account),("public_account",pack public_account),("checkpoint_account",pack checkpoint_account),("r",pack r),("cf",pack cf),("r1",pack r1),("cf1",pack cf1),("r2",pack r2),("cf2",pack cf2),("r3",pack r3),("cf3",pack cf3),("r4",pack r4),("cf4",pack cf4),("val",pack val),("r5",pack r5),("cf5",pack cf5),("r6",pack r6),("cf6",pack cf6),("val1",pack val1),("r7",pack r7),("cf7",pack cf7),("val2",pack val2),("r8",pack r8),("r9",pack r9),("cf8",pack cf8),("pvpftcv",pack pvpftcv),("r10",pack r10),("r11",pack r11),("cf9",pack cf9),("val3",pack val3),("r12",pack r12),("cf10",pack cf10),("val4",pack val4),("proof_length",pack proof_length),("proof_start",pack proof_start),("o",pack o),("r13",pack r13),("cf11",pack cf11),("residual",pack residual)] (
                                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                (alloc.vec.Vec Std.U8) (core.convert.FromSame
                                solana_program_error.ProgramError) residual
                              )
                          | core.ops.control_flow.ControlFlow.Break residual =>
                            call 3032 [("program_id",pack program_id),("accounts",pack accounts),("data",pack data),("b",pack b),("i",pack i),("proof_account",pack proof_account),("public_account",pack public_account),("checkpoint_account",pack checkpoint_account),("r",pack r),("cf",pack cf),("r1",pack r1),("cf1",pack cf1),("r2",pack r2),("cf2",pack cf2),("r3",pack r3),("cf3",pack cf3),("r4",pack r4),("cf4",pack cf4),("val",pack val),("r5",pack r5),("cf5",pack cf5),("r6",pack r6),("cf6",pack cf6),("val1",pack val1),("r7",pack r7),("cf7",pack cf7),("val2",pack val2),("r8",pack r8),("r9",pack r9),("cf8",pack cf8),("pvpftcv",pack pvpftcv),("r10",pack r10),("r11",pack r11),("cf9",pack cf9),("val3",pack val3),("r12",pack r12),("cf10",pack cf10),("residual",pack residual)] (
                              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                              (alloc.vec.Vec Std.U8) (core.convert.FromSame
                              solana_program_error.ProgramError) residual
                            )
                        | core.ops.control_flow.ControlFlow.Break residual =>
                          call 3036 [("program_id",pack program_id),("accounts",pack accounts),("data",pack data),("b",pack b),("i",pack i),("proof_account",pack proof_account),("public_account",pack public_account),("checkpoint_account",pack checkpoint_account),("r",pack r),("cf",pack cf),("r1",pack r1),("cf1",pack cf1),("r2",pack r2),("cf2",pack cf2),("r3",pack r3),("cf3",pack cf3),("r4",pack r4),("cf4",pack cf4),("val",pack val),("r5",pack r5),("cf5",pack cf5),("r6",pack r6),("cf6",pack cf6),("val1",pack val1),("r7",pack r7),("cf7",pack cf7),("val2",pack val2),("r8",pack r8),("r9",pack r9),("cf8",pack cf8),("pvpftcv",pack pvpftcv),("r10",pack r10),("r11",pack r11),("cf9",pack cf9),("residual",pack residual)] (
                            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                            (alloc.vec.Vec Std.U8) (core.convert.FromSame
                            solana_program_error.ProgramError) residual
                          )
                      | core.ops.control_flow.ControlFlow.Break residual =>
                        call 3040 [("program_id",pack program_id),("accounts",pack accounts),("data",pack data),("b",pack b),("i",pack i),("proof_account",pack proof_account),("public_account",pack public_account),("checkpoint_account",pack checkpoint_account),("r",pack r),("cf",pack cf),("r1",pack r1),("cf1",pack cf1),("r2",pack r2),("cf2",pack cf2),("r3",pack r3),("cf3",pack cf3),("r4",pack r4),("cf4",pack cf4),("val",pack val),("r5",pack r5),("cf5",pack cf5),("r6",pack r6),("cf6",pack cf6),("val1",pack val1),("r7",pack r7),("cf7",pack cf7),("val2",pack val2),("r8",pack r8),("r9",pack r9),("cf8",pack cf8),("residual",pack residual)] (
                          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                          (alloc.vec.Vec Std.U8) (core.convert.FromSame
                          solana_program_error.ProgramError) residual
                        )
                    | core.ops.control_flow.ControlFlow.Break residual =>
                      call 3044 [("program_id",pack program_id),("accounts",pack accounts),("data",pack data),("b",pack b),("i",pack i),("proof_account",pack proof_account),("public_account",pack public_account),("checkpoint_account",pack checkpoint_account),("r",pack r),("cf",pack cf),("r1",pack r1),("cf1",pack cf1),("r2",pack r2),("cf2",pack cf2),("r3",pack r3),("cf3",pack cf3),("r4",pack r4),("cf4",pack cf4),("val",pack val),("r5",pack r5),("cf5",pack cf5),("r6",pack r6),("cf6",pack cf6),("val1",pack val1),("r7",pack r7),("cf7",pack cf7),("residual",pack residual)] (
                        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                        (alloc.vec.Vec Std.U8) (core.convert.FromSame
                        solana_program_error.ProgramError) residual
                      )
                  | core.ops.control_flow.ControlFlow.Break residual =>
                    call 3048 [("program_id",pack program_id),("accounts",pack accounts),("data",pack data),("b",pack b),("i",pack i),("proof_account",pack proof_account),("public_account",pack public_account),("checkpoint_account",pack checkpoint_account),("r",pack r),("cf",pack cf),("r1",pack r1),("cf1",pack cf1),("r2",pack r2),("cf2",pack cf2),("r3",pack r3),("cf3",pack cf3),("r4",pack r4),("cf4",pack cf4),("val",pack val),("r5",pack r5),("cf5",pack cf5),("r6",pack r6),("cf6",pack cf6),("residual",pack residual)] (
                      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                      (alloc.vec.Vec Std.U8) (core.convert.FromSame
                      solana_program_error.ProgramError) residual
                    )
                | core.ops.control_flow.ControlFlow.Break residual =>
                  call 3052 [("program_id",pack program_id),("accounts",pack accounts),("data",pack data),("b",pack b),("i",pack i),("proof_account",pack proof_account),("public_account",pack public_account),("checkpoint_account",pack checkpoint_account),("r",pack r),("cf",pack cf),("r1",pack r1),("cf1",pack cf1),("r2",pack r2),("cf2",pack cf2),("r3",pack r3),("cf3",pack cf3),("r4",pack r4),("cf4",pack cf4),("val",pack val),("r5",pack r5),("cf5",pack cf5),("residual",pack residual)] (
                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                    (alloc.vec.Vec Std.U8) (core.convert.FromSame
                    solana_program_error.ProgramError) residual
                  )
              | core.ops.control_flow.ControlFlow.Break residual =>
                call 3056 [("program_id",pack program_id),("accounts",pack accounts),("data",pack data),("b",pack b),("i",pack i),("proof_account",pack proof_account),("public_account",pack public_account),("checkpoint_account",pack checkpoint_account),("r",pack r),("cf",pack cf),("r1",pack r1),("cf1",pack cf1),("r2",pack r2),("cf2",pack cf2),("r3",pack r3),("cf3",pack cf3),("r4",pack r4),("cf4",pack cf4),("residual",pack residual)] (
                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                  (alloc.vec.Vec Std.U8) (core.convert.FromSame
                  solana_program_error.ProgramError) residual
                )
            | core.ops.control_flow.ControlFlow.Break residual =>
              call 3060 [("program_id",pack program_id),("accounts",pack accounts),("data",pack data),("b",pack b),("i",pack i),("proof_account",pack proof_account),("public_account",pack public_account),("checkpoint_account",pack checkpoint_account),("r",pack r),("cf",pack cf),("r1",pack r1),("cf1",pack cf1),("r2",pack r2),("cf2",pack cf2),("r3",pack r3),("cf3",pack cf3),("residual",pack residual)] (
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                (alloc.vec.Vec Std.U8) (core.convert.FromSame
                solana_program_error.ProgramError) residual
              )
          | core.ops.control_flow.ControlFlow.Break residual =>
            call 3064 [("program_id",pack program_id),("accounts",pack accounts),("data",pack data),("b",pack b),("i",pack i),("proof_account",pack proof_account),("public_account",pack public_account),("checkpoint_account",pack checkpoint_account),("r",pack r),("cf",pack cf),("r1",pack r1),("cf1",pack cf1),("r2",pack r2),("cf2",pack cf2),("residual",pack residual)] (
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              (alloc.vec.Vec Std.U8) (core.convert.FromSame
              solana_program_error.ProgramError) residual
            )
        | core.ops.control_flow.ControlFlow.Break residual =>
          call 3068 [("program_id",pack program_id),("accounts",pack accounts),("data",pack data),("b",pack b),("i",pack i),("proof_account",pack proof_account),("public_account",pack public_account),("checkpoint_account",pack checkpoint_account),("r",pack r),("cf",pack cf),("r1",pack r1),("cf1",pack cf1),("residual",pack residual)] (
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            (alloc.vec.Vec Std.U8) (core.convert.FromSame
            solana_program_error.ProgramError) residual
          )
      | core.ops.control_flow.ControlFlow.Break residual =>
        call 3072 [("program_id",pack program_id),("accounts",pack accounts),("data",pack data),("b",pack b),("i",pack i),("proof_account",pack proof_account),("public_account",pack public_account),("checkpoint_account",pack checkpoint_account),("r",pack r),("cf",pack cf),("residual",pack residual)] (
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          (alloc.vec.Vec Std.U8) (core.convert.FromSame
          solana_program_error.ProgramError) residual
        )
  else
    let b1 ← call 3076 [("program_id",pack program_id),("accounts",pack accounts),("data",pack data),("b",pack b)] (
      ops.op1 core.cmp.PartialEqU8 data
        (Array.make 2#usize [ 3#u8, 11#u8 ])
    )
    if b1
    then
      let i := Slice.len accounts
      if i != 3#usize
      then
        NMB_TypedTrace.pure (core.result.Result.Err
          solana_program_error.ProgramError.InvalidInstructionData)
      else
        let proof_account ← call 3087 [("program_id",pack program_id),("accounts",pack accounts),("data",pack data),("b",pack b),("b1",pack b1),("i",pack i)] (
          Slice.index_usize accounts 0#usize
        )
        let public_account ← call 3088 [("program_id",pack program_id),("accounts",pack accounts),("data",pack data),("b",pack b),("b1",pack b1),("i",pack i),("proof_account",pack proof_account)] (
          Slice.index_usize accounts 1#usize
        )
        let checkpoint_account ← call 3089 [("program_id",pack program_id),("accounts",pack accounts),("data",pack data),("b",pack b),("b1",pack b1),("i",pack i),("proof_account",pack proof_account),("public_account",pack public_account)] (
          Slice.index_usize accounts 2#usize
        )
        let r ← call 3090 [("program_id",pack program_id),("accounts",pack accounts),("data",pack data),("b",pack b),("b1",pack b1),("i",pack i),("proof_account",pack proof_account),("public_account",pack public_account),("checkpoint_account",pack checkpoint_account)] (
          (r1_pool_adapter.owned.require_distinct_accounts ops)
            (Array.make 3#usize [
              proof_account, public_account, checkpoint_account
              ])
        )
        let cf ← call 3095 [("program_id",pack program_id),("accounts",pack accounts),("data",pack data),("b",pack b),("b1",pack b1),("i",pack i),("proof_account",pack proof_account),("public_account",pack public_account),("checkpoint_account",pack checkpoint_account),("r",pack r)] (
          core.result.Result.Insts.CoreOpsTry.branch r
        )
        match cf with
        | core.ops.control_flow.ControlFlow.Continue _ =>
          let r1 ← call 3098 [("program_id",pack program_id),("accounts",pack accounts),("data",pack data),("b",pack b),("b1",pack b1),("i",pack i),("proof_account",pack proof_account),("public_account",pack public_account),("checkpoint_account",pack checkpoint_account),("r",pack r),("cf",pack cf)] (
            r1_pool_adapter.owned.require_readonly_buffer proof_account
          )
          let cf1 ← call 3100 [("program_id",pack program_id),("accounts",pack accounts),("data",pack data),("b",pack b),("b1",pack b1),("i",pack i),("proof_account",pack proof_account),("public_account",pack public_account),("checkpoint_account",pack checkpoint_account),("r",pack r),("cf",pack cf),("r1",pack r1)] (
            core.result.Result.Insts.CoreOpsTry.branch r1
          )
          match cf1 with
          | core.ops.control_flow.ControlFlow.Continue _ =>
            let r2 ← call 3103 [("program_id",pack program_id),("accounts",pack accounts),("data",pack data),("b",pack b),("b1",pack b1),("i",pack i),("proof_account",pack proof_account),("public_account",pack public_account),("checkpoint_account",pack checkpoint_account),("r",pack r),("cf",pack cf),("r1",pack r1),("cf1",pack cf1)] (
              r1_pool_adapter.owned.require_readonly_buffer public_account
            )
            let cf2 ← call 3105 [("program_id",pack program_id),("accounts",pack accounts),("data",pack data),("b",pack b),("b1",pack b1),("i",pack i),("proof_account",pack proof_account),("public_account",pack public_account),("checkpoint_account",pack checkpoint_account),("r",pack r),("cf",pack cf),("r1",pack r1),("cf1",pack cf1),("r2",pack r2)] (
              core.result.Result.Insts.CoreOpsTry.branch r2
            )
            match cf2 with
            | core.ops.control_flow.ControlFlow.Continue _ =>
              let r3 ← call 3108 [("program_id",pack program_id),("accounts",pack accounts),("data",pack data),("b",pack b),("b1",pack b1),("i",pack i),("proof_account",pack proof_account),("public_account",pack public_account),("checkpoint_account",pack checkpoint_account),("r",pack r),("cf",pack cf),("r1",pack r1),("cf1",pack cf1),("r2",pack r2),("cf2",pack cf2)] (
                (r1_pool_adapter.owned.require_verifier_checkpoint ops)
                  checkpoint_account program_id true
              )
              let cf3 ← call 3111 [("program_id",pack program_id),("accounts",pack accounts),("data",pack data),("b",pack b),("b1",pack b1),("i",pack i),("proof_account",pack proof_account),("public_account",pack public_account),("checkpoint_account",pack checkpoint_account),("r",pack r),("cf",pack cf),("r1",pack r1),("cf1",pack cf1),("r2",pack r2),("cf2",pack cf2),("r3",pack r3)] (
                core.result.Result.Insts.CoreOpsTry.branch r3
              )
              match cf3 with
              | core.ops.control_flow.ControlFlow.Continue _ =>
                let r4 ← call 3114 [("program_id",pack program_id),("accounts",pack accounts),("data",pack data),("b",pack b),("b1",pack b1),("i",pack i),("proof_account",pack proof_account),("public_account",pack public_account),("checkpoint_account",pack checkpoint_account),("r",pack r),("cf",pack cf),("r1",pack r1),("cf1",pack cf1),("r2",pack r2),("cf2",pack cf2),("r3",pack r3),("cf3",pack cf3)] (
                  (r1_pool_adapter.owned.OwnedAccount.data ops) checkpoint_account
                )
                let cf4 ← call 3116 [("program_id",pack program_id),("accounts",pack accounts),("data",pack data),("b",pack b),("b1",pack b1),("i",pack i),("proof_account",pack proof_account),("public_account",pack public_account),("checkpoint_account",pack checkpoint_account),("r",pack r),("cf",pack cf),("r1",pack r1),("cf1",pack cf1),("r2",pack r2),("cf2",pack cf2),("r3",pack r3),("cf3",pack cf3),("r4",pack r4)] (
                  core.result.Result.Insts.CoreOpsTry.branch r4
                )
                match cf4 with
                | core.ops.control_flow.ControlFlow.Continue val =>
                  let r5 ← call 3119 [("program_id",pack program_id),("accounts",pack accounts),("data",pack data),("b",pack b),("b1",pack b1),("i",pack i),("proof_account",pack proof_account),("public_account",pack public_account),("checkpoint_account",pack checkpoint_account),("r",pack r),("cf",pack cf),("r1",pack r1),("cf1",pack cf1),("r2",pack r2),("cf2",pack cf2),("r3",pack r3),("cf3",pack cf3),("r4",pack r4),("cf4",pack cf4),("val",pack val)] (
                    r1_pool_adapter.owned.require_zero val
                  )
                  let cf5 ← call 3120 [("program_id",pack program_id),("accounts",pack accounts),("data",pack data),("b",pack b),("b1",pack b1),("i",pack i),("proof_account",pack proof_account),("public_account",pack public_account),("checkpoint_account",pack checkpoint_account),("r",pack r),("cf",pack cf),("r1",pack r1),("cf1",pack cf1),("r2",pack r2),("cf2",pack cf2),("r3",pack r3),("cf3",pack cf3),("r4",pack r4),("cf4",pack cf4),("val",pack val),("r5",pack r5)] (
                    core.result.Result.Insts.CoreOpsTry.branch r5
                  )
                  match cf5 with
                  | core.ops.control_flow.ControlFlow.Continue _ =>
                    let r6 ← call 3123 [("program_id",pack program_id),("accounts",pack accounts),("data",pack data),("b",pack b),("b1",pack b1),("i",pack i),("proof_account",pack proof_account),("public_account",pack public_account),("checkpoint_account",pack checkpoint_account),("r",pack r),("cf",pack cf),("r1",pack r1),("cf1",pack cf1),("r2",pack r2),("cf2",pack cf2),("r3",pack r3),("cf3",pack cf3),("r4",pack r4),("cf4",pack cf4),("val",pack val),("r5",pack r5),("cf5",pack cf5)] (
                      (r1_pool_adapter.owned.OwnedAccount.data ops) public_account
                    )
                    let cf6 ← call 3125 [("program_id",pack program_id),("accounts",pack accounts),("data",pack data),("b",pack b),("b1",pack b1),("i",pack i),("proof_account",pack proof_account),("public_account",pack public_account),("checkpoint_account",pack checkpoint_account),("r",pack r),("cf",pack cf),("r1",pack r1),("cf1",pack cf1),("r2",pack r2),("cf2",pack cf2),("r3",pack r3),("cf3",pack cf3),("r4",pack r4),("cf4",pack cf4),("val",pack val),("r5",pack r5),("cf5",pack cf5),("r6",pack r6)] (
                      core.result.Result.Insts.CoreOpsTry.branch r6
                    )
                    match cf6 with
                    | core.ops.control_flow.ControlFlow.Continue val1 =>
                      let r7 ← call 3128 [("program_id",pack program_id),("accounts",pack accounts),("data",pack data),("b",pack b),("b1",pack b1),("i",pack i),("proof_account",pack proof_account),("public_account",pack public_account),("checkpoint_account",pack checkpoint_account),("r",pack r),("cf",pack cf),("r1",pack r1),("cf1",pack cf1),("r2",pack r2),("cf2",pack cf2),("r3",pack r3),("cf3",pack cf3),("r4",pack r4),("cf4",pack cf4),("val",pack val),("r5",pack r5),("cf5",pack cf5),("r6",pack r6),("cf6",pack cf6),("val1",pack val1)] (
                        ops.op47 val1
                      )
                      let cf7 ← call 3130 [("program_id",pack program_id),("accounts",pack accounts),("data",pack data),("b",pack b),("b1",pack b1),("i",pack i),("proof_account",pack proof_account),("public_account",pack public_account),("checkpoint_account",pack checkpoint_account),("r",pack r),("cf",pack cf),("r1",pack r1),("cf1",pack cf1),("r2",pack r2),("cf2",pack cf2),("r3",pack r3),("cf3",pack cf3),("r4",pack r4),("cf4",pack cf4),("val",pack val),("r5",pack r5),("cf5",pack cf5),("r6",pack r6),("cf6",pack cf6),("val1",pack val1),("r7",pack r7)] (
                        core.result.Result.Insts.CoreOpsTry.branch r7
                      )
                      match cf7 with
                      | core.ops.control_flow.ControlFlow.Continue val2 =>
                        let r8 ← call 3133 [("program_id",pack program_id),("accounts",pack accounts),("data",pack data),("b",pack b),("b1",pack b1),("i",pack i),("proof_account",pack proof_account),("public_account",pack public_account),("checkpoint_account",pack checkpoint_account),("r",pack r),("cf",pack cf),("r1",pack r1),("cf1",pack cf1),("r2",pack r2),("cf2",pack cf2),("r3",pack r3),("cf3",pack cf3),("r4",pack r4),("cf4",pack cf4),("val",pack val),("r5",pack r5),("cf5",pack cf5),("r6",pack r6),("cf6",pack cf6),("val1",pack val1),("r7",pack r7),("cf7",pack cf7),("val2",pack val2)] (
                          ops.op21
                            val2
                        )
                        let r9 ← call 3136 [("program_id",pack program_id),("accounts",pack accounts),("data",pack data),("b",pack b),("b1",pack b1),("i",pack i),("proof_account",pack proof_account),("public_account",pack public_account),("checkpoint_account",pack checkpoint_account),("r",pack r),("cf",pack cf),("r1",pack r1),("cf1",pack cf1),("r2",pack r2),("cf2",pack cf2),("r3",pack r3),("cf3",pack cf3),("r4",pack r4),("cf4",pack cf4),("val",pack val),("r5",pack r5),("cf5",pack cf5),("r6",pack r6),("cf6",pack cf6),("val1",pack val1),("r7",pack r7),("cf7",pack cf7),("val2",pack val2),("r8",pack r8)] (
                          core.result.Result.map_err
                            r1_pool_adapter.owned.stage1_owned.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestTerminalFormatErrorV1ProgramError
                            r8 ()
                        )
                        let cf8 ← call 3140 [("program_id",pack program_id),("accounts",pack accounts),("data",pack data),("b",pack b),("b1",pack b1),("i",pack i),("proof_account",pack proof_account),("public_account",pack public_account),("checkpoint_account",pack checkpoint_account),("r",pack r),("cf",pack cf),("r1",pack r1),("cf1",pack cf1),("r2",pack r2),("cf2",pack cf2),("r3",pack r3),("cf3",pack cf3),("r4",pack r4),("cf4",pack cf4),("val",pack val),("r5",pack r5),("cf5",pack cf5),("r6",pack r6),("cf6",pack cf6),("val1",pack val1),("r7",pack r7),("cf7",pack cf7),("val2",pack val2),("r8",pack r8),("r9",pack r9)] (
                          core.result.Result.Insts.CoreOpsTry.branch r9
                        )
                        match cf8 with
                        | core.ops.control_flow.ControlFlow.Continue _ =>
                          let pvpftcv ← call 3144 [("program_id",pack program_id),("accounts",pack accounts),("data",pack data),("b",pack b),("b1",pack b1),("i",pack i),("proof_account",pack proof_account),("public_account",pack public_account),("checkpoint_account",pack checkpoint_account),("r",pack r),("cf",pack cf),("r1",pack r1),("cf1",pack cf1),("r2",pack r2),("cf2",pack cf2),("r3",pack r3),("cf3",pack cf3),("r4",pack r4),("cf4",pack cf4),("val",pack val),("r5",pack r5),("cf5",pack cf5),("r6",pack r6),("cf6",pack cf6),("val1",pack val1),("r7",pack r7),("cf7",pack cf7),("val2",pack val2),("r8",pack r8),("r9",pack r9),("cf8",pack cf8)] (
                            aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.common
                              val2
                          )
                          let r10 ← call 3147 [("program_id",pack program_id),("accounts",pack accounts),("data",pack data),("b",pack b),("b1",pack b1),("i",pack i),("proof_account",pack proof_account),("public_account",pack public_account),("checkpoint_account",pack checkpoint_account),("r",pack r),("cf",pack cf),("r1",pack r1),("cf1",pack cf1),("r2",pack r2),("cf2",pack cf2),("r3",pack r3),("cf3",pack cf3),("r4",pack r4),("cf4",pack cf4),("val",pack val),("r5",pack r5),("cf5",pack cf5),("r6",pack r6),("cf6",pack cf6),("val1",pack val1),("r7",pack r7),("cf7",pack cf7),("val2",pack val2),("r8",pack r8),("r9",pack r9),("cf8",pack cf8),("pvpftcv",pack pvpftcv)] (
                            ops.op24
                              pvpftcv.lane_transition.candidate_afterstate
                          )
                          let r11 ← call 3150 [("program_id",pack program_id),("accounts",pack accounts),("data",pack data),("b",pack b),("b1",pack b1),("i",pack i),("proof_account",pack proof_account),("public_account",pack public_account),("checkpoint_account",pack checkpoint_account),("r",pack r),("cf",pack cf),("r1",pack r1),("cf1",pack cf1),("r2",pack r2),("cf2",pack cf2),("r3",pack r3),("cf3",pack cf3),("r4",pack r4),("cf4",pack cf4),("val",pack val),("r5",pack r5),("cf5",pack cf5),("r6",pack r6),("cf6",pack cf6),("val1",pack val1),("r7",pack r7),("cf7",pack cf7),("val2",pack val2),("r8",pack r8),("r9",pack r9),("cf8",pack cf8),("pvpftcv",pack pvpftcv),("r10",pack r10)] (
                            core.result.Result.map_err
                              r1_pool_adapter.owned.stage1_owned.closure_1.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairVerifierTransportErrorV1ProgramError
                              r10 ()
                          )
                          let cf9 ← call 3154 [("program_id",pack program_id),("accounts",pack accounts),("data",pack data),("b",pack b),("b1",pack b1),("i",pack i),("proof_account",pack proof_account),("public_account",pack public_account),("checkpoint_account",pack checkpoint_account),("r",pack r),("cf",pack cf),("r1",pack r1),("cf1",pack cf1),("r2",pack r2),("cf2",pack cf2),("r3",pack r3),("cf3",pack cf3),("r4",pack r4),("cf4",pack cf4),("val",pack val),("r5",pack r5),("cf5",pack cf5),("r6",pack r6),("cf6",pack cf6),("val1",pack val1),("r7",pack r7),("cf7",pack cf7),("val2",pack val2),("r8",pack r8),("r9",pack r9),("cf8",pack cf8),("pvpftcv",pack pvpftcv),("r10",pack r10),("r11",pack r11)] (
                            core.result.Result.Insts.CoreOpsTry.branch r11
                          )
                          match cf9 with
                          | core.ops.control_flow.ControlFlow.Continue val3 =>
                            let r12 ← call 3158 [("program_id",pack program_id),("accounts",pack accounts),("data",pack data),("b",pack b),("b1",pack b1),("i",pack i),("proof_account",pack proof_account),("public_account",pack public_account),("checkpoint_account",pack checkpoint_account),("r",pack r),("cf",pack cf),("r1",pack r1),("cf1",pack cf1),("r2",pack r2),("cf2",pack cf2),("r3",pack r3),("cf3",pack cf3),("r4",pack r4),("cf4",pack cf4),("val",pack val),("r5",pack r5),("cf5",pack cf5),("r6",pack r6),("cf6",pack cf6),("val1",pack val1),("r7",pack r7),("cf7",pack cf7),("val2",pack val2),("r8",pack r8),("r9",pack r9),("cf8",pack cf8),("pvpftcv",pack pvpftcv),("r10",pack r10),("r11",pack r11),("cf9",pack cf9),("val3",pack val3)] (
                              (r1_pool_adapter.owned.OwnedAccount.data ops)
                                proof_account
                            )
                            let cf10 ← call 3161 [("program_id",pack program_id),("accounts",pack accounts),("data",pack data),("b",pack b),("b1",pack b1),("i",pack i),("proof_account",pack proof_account),("public_account",pack public_account),("checkpoint_account",pack checkpoint_account),("r",pack r),("cf",pack cf),("r1",pack r1),("cf1",pack cf1),("r2",pack r2),("cf2",pack cf2),("r3",pack r3),("cf3",pack cf3),("r4",pack r4),("cf4",pack cf4),("val",pack val),("r5",pack r5),("cf5",pack cf5),("r6",pack r6),("cf6",pack cf6),("val1",pack val1),("r7",pack r7),("cf7",pack cf7),("val2",pack val2),("r8",pack r8),("r9",pack r9),("cf8",pack cf8),("pvpftcv",pack pvpftcv),("r10",pack r10),("r11",pack r11),("cf9",pack cf9),("val3",pack val3),("r12",pack r12)] (
                              core.result.Result.Insts.CoreOpsTry.branch r12
                            )
                            match cf10 with
                            | core.ops.control_flow.ControlFlow.Continue val4
                              =>
                              let proof_length ← call 3166 [("program_id",pack program_id),("accounts",pack accounts),("data",pack data),("b",pack b),("b1",pack b1),("i",pack i),("proof_account",pack proof_account),("public_account",pack public_account),("checkpoint_account",pack checkpoint_account),("r",pack r),("cf",pack cf),("r1",pack r1),("cf1",pack cf1),("r2",pack r2),("cf2",pack cf2),("r3",pack r3),("cf3",pack cf3),("r4",pack r4),("cf4",pack cf4),("val",pack val),("r5",pack r5),("cf5",pack cf5),("r6",pack r6),("cf6",pack cf6),("val1",pack val1),("r7",pack r7),("cf7",pack cf7),("val2",pack val2),("r8",pack r8),("r9",pack r9),("cf8",pack cf8),("pvpftcv",pack pvpftcv),("r10",pack r10),("r11",pack r11),("cf9",pack cf9),("val3",pack val3),("r12",pack r12),("cf10",pack cf10),("val4",pack val4)] (
                                aspis_r1_cost_probe.verifier.PROOF_BYTES
                              )
                              let proof_start ← call 3168 [("program_id",pack program_id),("accounts",pack accounts),("data",pack data),("b",pack b),("b1",pack b1),("i",pack i),("proof_account",pack proof_account),("public_account",pack public_account),("checkpoint_account",pack checkpoint_account),("r",pack r),("cf",pack cf),("r1",pack r1),("cf1",pack cf1),("r2",pack r2),("cf2",pack cf2),("r3",pack r3),("cf3",pack cf3),("r4",pack r4),("cf4",pack cf4),("val",pack val),("r5",pack r5),("cf5",pack cf5),("r6",pack r6),("cf6",pack cf6),("val1",pack val1),("r7",pack r7),("cf7",pack cf7),("val2",pack val2),("r8",pack r8),("r9",pack r9),("cf8",pack cf8),("pvpftcv",pack pvpftcv),("r10",pack r10),("r11",pack r11),("cf9",pack cf9),("val3",pack val3),("r12",pack r12),("cf10",pack cf10),("val4",pack val4),("proof_length",pack proof_length)] (
                                (aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES ops)
                              )
                              let o ← call 3170 [("program_id",pack program_id),("accounts",pack accounts),("data",pack data),("b",pack b),("b1",pack b1),("i",pack i),("proof_account",pack proof_account),("public_account",pack public_account),("checkpoint_account",pack checkpoint_account),("r",pack r),("cf",pack cf),("r1",pack r1),("cf1",pack cf1),("r2",pack r2),("cf2",pack cf2),("r3",pack r3),("cf3",pack cf3),("r4",pack r4),("cf4",pack cf4),("val",pack val),("r5",pack r5),("cf5",pack cf5),("r6",pack r6),("cf6",pack cf6),("val1",pack val1),("r7",pack r7),("cf7",pack cf7),("val2",pack val2),("r8",pack r8),("r9",pack r9),("cf8",pack cf8),("pvpftcv",pack pvpftcv),("r10",pack r10),("r11",pack r11),("cf9",pack cf9),("val3",pack val3),("r12",pack r12),("cf10",pack cf10),("val4",pack val4),("proof_length",pack proof_length),("proof_start",pack proof_start)] (
                                lift (Usize.checked_add proof_start
                                  proof_length)
                              )
                              let r13 ← call 3173 [("program_id",pack program_id),("accounts",pack accounts),("data",pack data),("b",pack b),("b1",pack b1),("i",pack i),("proof_account",pack proof_account),("public_account",pack public_account),("checkpoint_account",pack checkpoint_account),("r",pack r),("cf",pack cf),("r1",pack r1),("cf1",pack cf1),("r2",pack r2),("cf2",pack cf2),("r3",pack r3),("cf3",pack cf3),("r4",pack r4),("cf4",pack cf4),("val",pack val),("r5",pack r5),("cf5",pack cf5),("r6",pack r6),("cf6",pack cf6),("val1",pack val1),("r7",pack r7),("cf7",pack cf7),("val2",pack val2),("r8",pack r8),("r9",pack r9),("cf8",pack cf8),("pvpftcv",pack pvpftcv),("r10",pack r10),("r11",pack r11),("cf9",pack cf9),("val3",pack val3),("r12",pack r12),("cf10",pack cf10),("val4",pack val4),("proof_length",pack proof_length),("proof_start",pack proof_start),("o",pack o)] (
                                core.option.Option.ok_or o
                                  solana_program_error.ProgramError.InvalidAccountData
                              )
                              let cf11 ← call 3176 [("program_id",pack program_id),("accounts",pack accounts),("data",pack data),("b",pack b),("b1",pack b1),("i",pack i),("proof_account",pack proof_account),("public_account",pack public_account),("checkpoint_account",pack checkpoint_account),("r",pack r),("cf",pack cf),("r1",pack r1),("cf1",pack cf1),("r2",pack r2),("cf2",pack cf2),("r3",pack r3),("cf3",pack cf3),("r4",pack r4),("cf4",pack cf4),("val",pack val),("r5",pack r5),("cf5",pack cf5),("r6",pack r6),("cf6",pack cf6),("val1",pack val1),("r7",pack r7),("cf7",pack cf7),("val2",pack val2),("r8",pack r8),("r9",pack r9),("cf8",pack cf8),("pvpftcv",pack pvpftcv),("r10",pack r10),("r11",pack r11),("cf9",pack cf9),("val3",pack val3),("r12",pack r12),("cf10",pack cf10),("val4",pack val4),("proof_length",pack proof_length),("proof_start",pack proof_start),("o",pack o),("r13",pack r13)] (
                                core.result.Result.Insts.CoreOpsTry.branch r13
                              )
                              match cf11 with
                              | core.ops.control_flow.ControlFlow.Continue val5
                                =>
                                let i1 := Slice.len val4
                                if i1 != val5
                                then
                                  NMB_TypedTrace.pure (core.result.Result.Err
                                    solana_program_error.ProgramError.InvalidAccountData)
                                else
                                  let s ← call 3187 [("program_id",pack program_id),("accounts",pack accounts),("data",pack data),("b",pack b),("b1",pack b1),("i",pack i),("proof_account",pack proof_account),("public_account",pack public_account),("checkpoint_account",pack checkpoint_account),("r",pack r),("cf",pack cf),("r1",pack r1),("cf1",pack cf1),("r2",pack r2),("cf2",pack cf2),("r3",pack r3),("cf3",pack cf3),("r4",pack r4),("cf4",pack cf4),("val",pack val),("r5",pack r5),("cf5",pack cf5),("r6",pack r6),("cf6",pack cf6),("val1",pack val1),("r7",pack r7),("cf7",pack cf7),("val2",pack val2),("r8",pack r8),("r9",pack r9),("cf8",pack cf8),("pvpftcv",pack pvpftcv),("r10",pack r10),("r11",pack r11),("cf9",pack cf9),("val3",pack val3),("r12",pack r12),("cf10",pack cf10),("val4",pack val4),("proof_length",pack proof_length),("proof_start",pack proof_start),("o",pack o),("r13",pack r13),("cf11",pack cf11),("val5",pack val5),("i1",pack i1)] (
                                    core.slice.index.Slice.index
                                      (core.slice.index.SliceIndexRangeToUsizeSlice
                                      Std.U8) val4 { «end» := proof_start }
                                  )
                                  let b2 ← call 3191 [("program_id",pack program_id),("accounts",pack accounts),("data",pack data),("b",pack b),("b1",pack b1),("i",pack i),("proof_account",pack proof_account),("public_account",pack public_account),("checkpoint_account",pack checkpoint_account),("r",pack r),("cf",pack cf),("r1",pack r1),("cf1",pack cf1),("r2",pack r2),("cf2",pack cf2),("r3",pack r3),("cf3",pack cf3),("r4",pack r4),("cf4",pack cf4),("val",pack val),("r5",pack r5),("cf5",pack cf5),("r6",pack r6),("cf6",pack cf6),("val1",pack val1),("r7",pack r7),("cf7",pack cf7),("val2",pack val2),("r8",pack r8),("r9",pack r9),("cf8",pack cf8),("pvpftcv",pack pvpftcv),("r10",pack r10),("r11",pack r11),("cf9",pack cf9),("val3",pack val3),("r12",pack r12),("cf10",pack cf10),("val4",pack val4),("proof_length",pack proof_length),("proof_start",pack proof_start),("o",pack o),("r13",pack r13),("cf11",pack cf11),("val5",pack val5),("i1",pack i1),("s",pack s)] (
                                    ops.op0
                                      core.cmp.PartialEqU8 s val3
                                  )
                                  if b2
                                  then
                                    NMB_TypedTrace.pure (core.result.Result.Err
                                      solana_program_error.ProgramError.InvalidAccountData)
                                  else
                                    let i2 ← call 3199 [("program_id",pack program_id),("accounts",pack accounts),("data",pack data),("b",pack b),("b1",pack b1),("i",pack i),("proof_account",pack proof_account),("public_account",pack public_account),("checkpoint_account",pack checkpoint_account),("r",pack r),("cf",pack cf),("r1",pack r1),("cf1",pack cf1),("r2",pack r2),("cf2",pack cf2),("r3",pack r3),("cf3",pack cf3),("r4",pack r4),("cf4",pack cf4),("val",pack val),("r5",pack r5),("cf5",pack cf5),("r6",pack r6),("cf6",pack cf6),("val1",pack val1),("r7",pack r7),("cf7",pack cf7),("val2",pack val2),("r8",pack r8),("r9",pack r9),("cf8",pack cf8),("pvpftcv",pack pvpftcv),("r10",pack r10),("r11",pack r11),("cf9",pack cf9),("val3",pack val3),("r12",pack r12),("cf10",pack cf10),("val4",pack val4),("proof_length",pack proof_length),("proof_start",pack proof_start),("o",pack o),("r13",pack r13),("cf11",pack cf11),("val5",pack val5),("i1",pack i1),("s",pack s),("b2",pack b2)] (
                                      lift (Std.Usize.wrapping_add proof_start
                                        8#usize)
                                    )
                                    let i3 ← call 3202 [("program_id",pack program_id),("accounts",pack accounts),("data",pack data),("b",pack b),("b1",pack b1),("i",pack i),("proof_account",pack proof_account),("public_account",pack public_account),("checkpoint_account",pack checkpoint_account),("r",pack r),("cf",pack cf),("r1",pack r1),("cf1",pack cf1),("r2",pack r2),("cf2",pack cf2),("r3",pack r3),("cf3",pack cf3),("r4",pack r4),("cf4",pack cf4),("val",pack val),("r5",pack r5),("cf5",pack cf5),("r6",pack r6),("cf6",pack cf6),("val1",pack val1),("r7",pack r7),("cf7",pack cf7),("val2",pack val2),("r8",pack r8),("r9",pack r9),("cf8",pack cf8),("pvpftcv",pack pvpftcv),("r10",pack r10),("r11",pack r11),("cf9",pack cf9),("val3",pack val3),("r12",pack r12),("cf10",pack cf10),("val4",pack val4),("proof_length",pack proof_length),("proof_start",pack proof_start),("o",pack o),("r13",pack r13),("cf11",pack cf11),("val5",pack val5),("i1",pack i1),("s",pack s),("b2",pack b2),("i2",pack i2)] (
                                      Slice.index_usize val4 i2
                                    )
                                    let i4 ← call 3203 [("program_id",pack program_id),("accounts",pack accounts),("data",pack data),("b",pack b),("b1",pack b1),("i",pack i),("proof_account",pack proof_account),("public_account",pack public_account),("checkpoint_account",pack checkpoint_account),("r",pack r),("cf",pack cf),("r1",pack r1),("cf1",pack cf1),("r2",pack r2),("cf2",pack cf2),("r3",pack r3),("cf3",pack cf3),("r4",pack r4),("cf4",pack cf4),("val",pack val),("r5",pack r5),("cf5",pack cf5),("r6",pack r6),("cf6",pack cf6),("val1",pack val1),("r7",pack r7),("cf7",pack cf7),("val2",pack val2),("r8",pack r8),("r9",pack r9),("cf8",pack cf8),("pvpftcv",pack pvpftcv),("r10",pack r10),("r11",pack r11),("cf9",pack cf9),("val3",pack val3),("r12",pack r12),("cf10",pack cf10),("val4",pack val4),("proof_length",pack proof_length),("proof_start",pack proof_start),("o",pack o),("r13",pack r13),("cf11",pack cf11),("val5",pack val5),("i1",pack i1),("s",pack s),("b2",pack b2),("i2",pack i2),("i3",pack i3)] (
                                      aspis_r1_cost_probe.transport.Variant.tag
                                        aspis_r1_cost_probe.transport.Variant.S2
                                    )
                                    if i3 != i4
                                    then
                                      NMB_TypedTrace.pure (core.result.Result.Err
                                        solana_program_error.ProgramError.InvalidAccountData)
                                    else
                                      let p ← call 3211 [("program_id",pack program_id),("accounts",pack accounts),("data",pack data),("b",pack b),("b1",pack b1),("i",pack i),("proof_account",pack proof_account),("public_account",pack public_account),("checkpoint_account",pack checkpoint_account),("r",pack r),("cf",pack cf),("r1",pack r1),("cf1",pack cf1),("r2",pack r2),("cf2",pack cf2),("r3",pack r3),("cf3",pack cf3),("r4",pack r4),("cf4",pack cf4),("val",pack val),("r5",pack r5),("cf5",pack cf5),("r6",pack r6),("cf6",pack cf6),("val1",pack val1),("r7",pack r7),("cf7",pack cf7),("val2",pack val2),("r8",pack r8),("r9",pack r9),("cf8",pack cf8),("pvpftcv",pack pvpftcv),("r10",pack r10),("r11",pack r11),("cf9",pack cf9),("val3",pack val3),("r12",pack r12),("cf10",pack cf10),("val4",pack val4),("proof_length",pack proof_length),("proof_start",pack proof_start),("o",pack o),("r13",pack r13),("cf11",pack cf11),("val5",pack val5),("i1",pack i1),("s",pack s),("b2",pack b2),("i2",pack i2),("i3",pack i3),("i4",pack i4)] (
                                        aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public
                                          val2
                                      )
                                      let s1 ← call 3214 [("program_id",pack program_id),("accounts",pack accounts),("data",pack data),("b",pack b),("b1",pack b1),("i",pack i),("proof_account",pack proof_account),("public_account",pack public_account),("checkpoint_account",pack checkpoint_account),("r",pack r),("cf",pack cf),("r1",pack r1),("cf1",pack cf1),("r2",pack r2),("cf2",pack cf2),("r3",pack r3),("cf3",pack cf3),("r4",pack r4),("cf4",pack cf4),("val",pack val),("r5",pack r5),("cf5",pack cf5),("r6",pack r6),("cf6",pack cf6),("val1",pack val1),("r7",pack r7),("cf7",pack cf7),("val2",pack val2),("r8",pack r8),("r9",pack r9),("cf8",pack cf8),("pvpftcv",pack pvpftcv),("r10",pack r10),("r11",pack r11),("cf9",pack cf9),("val3",pack val3),("r12",pack r12),("cf10",pack cf10),("val4",pack val4),("proof_length",pack proof_length),("proof_start",pack proof_start),("o",pack o),("r13",pack r13),("cf11",pack cf11),("val5",pack val5),("i1",pack i1),("s",pack s),("b2",pack b2),("i2",pack i2),("i3",pack i3),("i4",pack i4),("p",pack p)] (
                                        core.slice.index.Slice.index
                                          (core.slice.index.SliceIndexRangeUsizeSlice
                                          Std.U8) val4
                                          {
                                            start := proof_start,
                                            «end» := val5
                                          }
                                      )
                                      let i5 ← call 3222 [("program_id",pack program_id),("accounts",pack accounts),("data",pack data),("b",pack b),("b1",pack b1),("i",pack i),("proof_account",pack proof_account),("public_account",pack public_account),("checkpoint_account",pack checkpoint_account),("r",pack r),("cf",pack cf),("r1",pack r1),("cf1",pack cf1),("r2",pack r2),("cf2",pack cf2),("r3",pack r3),("cf3",pack cf3),("r4",pack r4),("cf4",pack cf4),("val",pack val),("r5",pack r5),("cf5",pack cf5),("r6",pack r6),("cf6",pack cf6),("val1",pack val1),("r7",pack r7),("cf7",pack cf7),("val2",pack val2),("r8",pack r8),("r9",pack r9),("cf8",pack cf8),("pvpftcv",pack pvpftcv),("r10",pack r10),("r11",pack r11),("cf9",pack cf9),("val3",pack val3),("r12",pack r12),("cf10",pack cf10),("val4",pack val4),("proof_length",pack proof_length),("proof_start",pack proof_start),("o",pack o),("r13",pack r13),("cf11",pack cf11),("val5",pack val5),("i1",pack i1),("s",pack s),("b2",pack b2),("i2",pack i2),("i3",pack i3),("i4",pack i4),("p",pack p),("s1",pack s1)] (
                                        Slice.index_usize data 1#usize
                                      )
                                      let i6 ← call 3223 [("program_id",pack program_id),("accounts",pack accounts),("data",pack data),("b",pack b),("b1",pack b1),("i",pack i),("proof_account",pack proof_account),("public_account",pack public_account),("checkpoint_account",pack checkpoint_account),("r",pack r),("cf",pack cf),("r1",pack r1),("cf1",pack cf1),("r2",pack r2),("cf2",pack cf2),("r3",pack r3),("cf3",pack cf3),("r4",pack r4),("cf4",pack cf4),("val",pack val),("r5",pack r5),("cf5",pack cf5),("r6",pack r6),("cf6",pack cf6),("val1",pack val1),("r7",pack r7),("cf7",pack cf7),("val2",pack val2),("r8",pack r8),("r9",pack r9),("cf8",pack cf8),("pvpftcv",pack pvpftcv),("r10",pack r10),("r11",pack r11),("cf9",pack cf9),("val3",pack val3),("r12",pack r12),("cf10",pack cf10),("val4",pack val4),("proof_length",pack proof_length),("proof_start",pack proof_start),("o",pack o),("r13",pack r13),("cf11",pack cf11),("val5",pack val5),("i1",pack i1),("s",pack s),("b2",pack b2),("i2",pack i2),("i3",pack i3),("i4",pack i4),("p",pack p),("s1",pack s1),("i5",pack i5)] (
                                        lift (UScalar.cast .Usize i5)
                                      )
                                      let r14 ← call 3224 [("program_id",pack program_id),("accounts",pack accounts),("data",pack data),("b",pack b),("b1",pack b1),("i",pack i),("proof_account",pack proof_account),("public_account",pack public_account),("checkpoint_account",pack checkpoint_account),("r",pack r),("cf",pack cf),("r1",pack r1),("cf1",pack cf1),("r2",pack r2),("cf2",pack cf2),("r3",pack r3),("cf3",pack cf3),("r4",pack r4),("cf4",pack cf4),("val",pack val),("r5",pack r5),("cf5",pack cf5),("r6",pack r6),("cf6",pack cf6),("val1",pack val1),("r7",pack r7),("cf7",pack cf7),("val2",pack val2),("r8",pack r8),("r9",pack r9),("cf8",pack cf8),("pvpftcv",pack pvpftcv),("r10",pack r10),("r11",pack r11),("cf9",pack cf9),("val3",pack val3),("r12",pack r12),("cf10",pack cf10),("val4",pack val4),("proof_length",pack proof_length),("proof_start",pack proof_start),("o",pack o),("r13",pack r13),("cf11",pack cf11),("val5",pack val5),("i1",pack i1),("s",pack s),("b2",pack b2),("i2",pack i2),("i3",pack i3),("i4",pack i4),("p",pack p),("s1",pack s1),("i5",pack i5),("i6",pack i6)] (
                                        (first_decoded ops) p val1 s1 i6
                                      )
                                      let cf12 ← call 3225 [("program_id",pack program_id),("accounts",pack accounts),("data",pack data),("b",pack b),("b1",pack b1),("i",pack i),("proof_account",pack proof_account),("public_account",pack public_account),("checkpoint_account",pack checkpoint_account),("r",pack r),("cf",pack cf),("r1",pack r1),("cf1",pack cf1),("r2",pack r2),("cf2",pack cf2),("r3",pack r3),("cf3",pack cf3),("r4",pack r4),("cf4",pack cf4),("val",pack val),("r5",pack r5),("cf5",pack cf5),("r6",pack r6),("cf6",pack cf6),("val1",pack val1),("r7",pack r7),("cf7",pack cf7),("val2",pack val2),("r8",pack r8),("r9",pack r9),("cf8",pack cf8),("pvpftcv",pack pvpftcv),("r10",pack r10),("r11",pack r11),("cf9",pack cf9),("val3",pack val3),("r12",pack r12),("cf10",pack cf10),("val4",pack val4),("proof_length",pack proof_length),("proof_start",pack proof_start),("o",pack o),("r13",pack r13),("cf11",pack cf11),("val5",pack val5),("i1",pack i1),("s",pack s),("b2",pack b2),("i2",pack i2),("i3",pack i3),("i4",pack i4),("p",pack p),("s1",pack s1),("i5",pack i5),("i6",pack i6),("r14",pack r14)] (
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
                                          NMB_TypedTrace.pure (core.result.Result.Err
                                            solana_program_error.ProgramError.InvalidAccountData)
                                        else NMB_TypedTrace.pure (core.result.Result.Ok val6)
                                      | core.ops.control_flow.ControlFlow.Break
                                        residual =>
                                        call 3241 [("program_id",pack program_id),("accounts",pack accounts),("data",pack data),("b",pack b),("b1",pack b1),("i",pack i),("proof_account",pack proof_account),("public_account",pack public_account),("checkpoint_account",pack checkpoint_account),("r",pack r),("cf",pack cf),("r1",pack r1),("cf1",pack cf1),("r2",pack r2),("cf2",pack cf2),("r3",pack r3),("cf3",pack cf3),("r4",pack r4),("cf4",pack cf4),("val",pack val),("r5",pack r5),("cf5",pack cf5),("r6",pack r6),("cf6",pack cf6),("val1",pack val1),("r7",pack r7),("cf7",pack cf7),("val2",pack val2),("r8",pack r8),("r9",pack r9),("cf8",pack cf8),("pvpftcv",pack pvpftcv),("r10",pack r10),("r11",pack r11),("cf9",pack cf9),("val3",pack val3),("r12",pack r12),("cf10",pack cf10),("val4",pack val4),("proof_length",pack proof_length),("proof_start",pack proof_start),("o",pack o),("r13",pack r13),("cf11",pack cf11),("val5",pack val5),("i1",pack i1),("s",pack s),("b2",pack b2),("i2",pack i2),("i3",pack i3),("i4",pack i4),("p",pack p),("s1",pack s1),("i5",pack i5),("i6",pack i6),("r14",pack r14),("cf12",pack cf12)] (
                                          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                          (alloc.vec.Vec Std.U8)
                                          (core.convert.FromSame
                                          solana_program_error.ProgramError)
                                          residual
                                        )
                              | core.ops.control_flow.ControlFlow.Break
                                residual =>
                                call 3248 [("program_id",pack program_id),("accounts",pack accounts),("data",pack data),("b",pack b),("b1",pack b1),("i",pack i),("proof_account",pack proof_account),("public_account",pack public_account),("checkpoint_account",pack checkpoint_account),("r",pack r),("cf",pack cf),("r1",pack r1),("cf1",pack cf1),("r2",pack r2),("cf2",pack cf2),("r3",pack r3),("cf3",pack cf3),("r4",pack r4),("cf4",pack cf4),("val",pack val),("r5",pack r5),("cf5",pack cf5),("r6",pack r6),("cf6",pack cf6),("val1",pack val1),("r7",pack r7),("cf7",pack cf7),("val2",pack val2),("r8",pack r8),("r9",pack r9),("cf8",pack cf8),("pvpftcv",pack pvpftcv),("r10",pack r10),("r11",pack r11),("cf9",pack cf9),("val3",pack val3),("r12",pack r12),("cf10",pack cf10),("val4",pack val4),("proof_length",pack proof_length),("proof_start",pack proof_start),("o",pack o),("r13",pack r13),("cf11",pack cf11)] (
                                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                  (alloc.vec.Vec Std.U8) (core.convert.FromSame
                                  solana_program_error.ProgramError) residual
                                )
                            | core.ops.control_flow.ControlFlow.Break residual
                              =>
                              call 3253 [("program_id",pack program_id),("accounts",pack accounts),("data",pack data),("b",pack b),("b1",pack b1),("i",pack i),("proof_account",pack proof_account),("public_account",pack public_account),("checkpoint_account",pack checkpoint_account),("r",pack r),("cf",pack cf),("r1",pack r1),("cf1",pack cf1),("r2",pack r2),("cf2",pack cf2),("r3",pack r3),("cf3",pack cf3),("r4",pack r4),("cf4",pack cf4),("val",pack val),("r5",pack r5),("cf5",pack cf5),("r6",pack r6),("cf6",pack cf6),("val1",pack val1),("r7",pack r7),("cf7",pack cf7),("val2",pack val2),("r8",pack r8),("r9",pack r9),("cf8",pack cf8),("pvpftcv",pack pvpftcv),("r10",pack r10),("r11",pack r11),("cf9",pack cf9),("val3",pack val3),("r12",pack r12),("cf10",pack cf10),("residual",pack residual)] (
                                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                                (alloc.vec.Vec Std.U8) (core.convert.FromSame
                                solana_program_error.ProgramError) residual
                              )
                          | core.ops.control_flow.ControlFlow.Break residual =>
                            call 3257 [("program_id",pack program_id),("accounts",pack accounts),("data",pack data),("b",pack b),("b1",pack b1),("i",pack i),("proof_account",pack proof_account),("public_account",pack public_account),("checkpoint_account",pack checkpoint_account),("r",pack r),("cf",pack cf),("r1",pack r1),("cf1",pack cf1),("r2",pack r2),("cf2",pack cf2),("r3",pack r3),("cf3",pack cf3),("r4",pack r4),("cf4",pack cf4),("val",pack val),("r5",pack r5),("cf5",pack cf5),("r6",pack r6),("cf6",pack cf6),("val1",pack val1),("r7",pack r7),("cf7",pack cf7),("val2",pack val2),("r8",pack r8),("r9",pack r9),("cf8",pack cf8),("pvpftcv",pack pvpftcv),("r10",pack r10),("r11",pack r11),("cf9",pack cf9),("residual",pack residual)] (
                              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                              (alloc.vec.Vec Std.U8) (core.convert.FromSame
                              solana_program_error.ProgramError) residual
                            )
                        | core.ops.control_flow.ControlFlow.Break residual =>
                          call 3261 [("program_id",pack program_id),("accounts",pack accounts),("data",pack data),("b",pack b),("b1",pack b1),("i",pack i),("proof_account",pack proof_account),("public_account",pack public_account),("checkpoint_account",pack checkpoint_account),("r",pack r),("cf",pack cf),("r1",pack r1),("cf1",pack cf1),("r2",pack r2),("cf2",pack cf2),("r3",pack r3),("cf3",pack cf3),("r4",pack r4),("cf4",pack cf4),("val",pack val),("r5",pack r5),("cf5",pack cf5),("r6",pack r6),("cf6",pack cf6),("val1",pack val1),("r7",pack r7),("cf7",pack cf7),("val2",pack val2),("r8",pack r8),("r9",pack r9),("cf8",pack cf8),("residual",pack residual)] (
                            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                            (alloc.vec.Vec Std.U8) (core.convert.FromSame
                            solana_program_error.ProgramError) residual
                          )
                      | core.ops.control_flow.ControlFlow.Break residual =>
                        call 3265 [("program_id",pack program_id),("accounts",pack accounts),("data",pack data),("b",pack b),("b1",pack b1),("i",pack i),("proof_account",pack proof_account),("public_account",pack public_account),("checkpoint_account",pack checkpoint_account),("r",pack r),("cf",pack cf),("r1",pack r1),("cf1",pack cf1),("r2",pack r2),("cf2",pack cf2),("r3",pack r3),("cf3",pack cf3),("r4",pack r4),("cf4",pack cf4),("val",pack val),("r5",pack r5),("cf5",pack cf5),("r6",pack r6),("cf6",pack cf6),("val1",pack val1),("r7",pack r7),("cf7",pack cf7),("residual",pack residual)] (
                          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                          (alloc.vec.Vec Std.U8) (core.convert.FromSame
                          solana_program_error.ProgramError) residual
                        )
                    | core.ops.control_flow.ControlFlow.Break residual =>
                      call 3269 [("program_id",pack program_id),("accounts",pack accounts),("data",pack data),("b",pack b),("b1",pack b1),("i",pack i),("proof_account",pack proof_account),("public_account",pack public_account),("checkpoint_account",pack checkpoint_account),("r",pack r),("cf",pack cf),("r1",pack r1),("cf1",pack cf1),("r2",pack r2),("cf2",pack cf2),("r3",pack r3),("cf3",pack cf3),("r4",pack r4),("cf4",pack cf4),("val",pack val),("r5",pack r5),("cf5",pack cf5),("r6",pack r6),("cf6",pack cf6),("residual",pack residual)] (
                        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                        (alloc.vec.Vec Std.U8) (core.convert.FromSame
                        solana_program_error.ProgramError) residual
                      )
                  | core.ops.control_flow.ControlFlow.Break residual =>
                    call 3273 [("program_id",pack program_id),("accounts",pack accounts),("data",pack data),("b",pack b),("b1",pack b1),("i",pack i),("proof_account",pack proof_account),("public_account",pack public_account),("checkpoint_account",pack checkpoint_account),("r",pack r),("cf",pack cf),("r1",pack r1),("cf1",pack cf1),("r2",pack r2),("cf2",pack cf2),("r3",pack r3),("cf3",pack cf3),("r4",pack r4),("cf4",pack cf4),("val",pack val),("r5",pack r5),("cf5",pack cf5),("residual",pack residual)] (
                      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                      (alloc.vec.Vec Std.U8) (core.convert.FromSame
                      solana_program_error.ProgramError) residual
                    )
                | core.ops.control_flow.ControlFlow.Break residual =>
                  call 3277 [("program_id",pack program_id),("accounts",pack accounts),("data",pack data),("b",pack b),("b1",pack b1),("i",pack i),("proof_account",pack proof_account),("public_account",pack public_account),("checkpoint_account",pack checkpoint_account),("r",pack r),("cf",pack cf),("r1",pack r1),("cf1",pack cf1),("r2",pack r2),("cf2",pack cf2),("r3",pack r3),("cf3",pack cf3),("r4",pack r4),("cf4",pack cf4),("residual",pack residual)] (
                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                    (alloc.vec.Vec Std.U8) (core.convert.FromSame
                    solana_program_error.ProgramError) residual
                  )
              | core.ops.control_flow.ControlFlow.Break residual =>
                call 3281 [("program_id",pack program_id),("accounts",pack accounts),("data",pack data),("b",pack b),("b1",pack b1),("i",pack i),("proof_account",pack proof_account),("public_account",pack public_account),("checkpoint_account",pack checkpoint_account),("r",pack r),("cf",pack cf),("r1",pack r1),("cf1",pack cf1),("r2",pack r2),("cf2",pack cf2),("r3",pack r3),("cf3",pack cf3),("residual",pack residual)] (
                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                  (alloc.vec.Vec Std.U8) (core.convert.FromSame
                  solana_program_error.ProgramError) residual
                )
            | core.ops.control_flow.ControlFlow.Break residual =>
              call 3285 [("program_id",pack program_id),("accounts",pack accounts),("data",pack data),("b",pack b),("b1",pack b1),("i",pack i),("proof_account",pack proof_account),("public_account",pack public_account),("checkpoint_account",pack checkpoint_account),("r",pack r),("cf",pack cf),("r1",pack r1),("cf1",pack cf1),("r2",pack r2),("cf2",pack cf2),("residual",pack residual)] (
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                (alloc.vec.Vec Std.U8) (core.convert.FromSame
                solana_program_error.ProgramError) residual
              )
          | core.ops.control_flow.ControlFlow.Break residual =>
            call 3289 [("program_id",pack program_id),("accounts",pack accounts),("data",pack data),("b",pack b),("b1",pack b1),("i",pack i),("proof_account",pack proof_account),("public_account",pack public_account),("checkpoint_account",pack checkpoint_account),("r",pack r),("cf",pack cf),("r1",pack r1),("cf1",pack cf1),("residual",pack residual)] (
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              (alloc.vec.Vec Std.U8) (core.convert.FromSame
              solana_program_error.ProgramError) residual
            )
        | core.ops.control_flow.ControlFlow.Break residual =>
          call 3293 [("program_id",pack program_id),("accounts",pack accounts),("data",pack data),("b",pack b),("b1",pack b1),("i",pack i),("proof_account",pack proof_account),("public_account",pack public_account),("checkpoint_account",pack checkpoint_account),("r",pack r),("cf",pack cf),("residual",pack residual)] (
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            (alloc.vec.Vec Std.U8) (core.convert.FromSame
            solana_program_error.ProgramError) residual
          )
    else
      NMB_TypedTrace.pure (core.result.Result.Err
        solana_program_error.ProgramError.InvalidInstructionData)

attribute [local irreducible] NMB_TypedTrace.forget NMB_TypedTrace.bind NMB_TypedTrace.pure NMB_TypedTrace.call
theorem forget_eq (ops : AdapterRw.Ops) (program : AdapterRw.solana_pubkey.Pubkey)
 (accounts : Slice AdapterRw.r1_pool_adapter.owned.OwnedAccount) (data : Slice U8) :
 forget (stage1Owned ops program accounts data)=
 AspisR1.NLD_Stage1Source.stage1Owned ops program accounts data := by
 unfold stage1Owned AspisR1.NLD_Stage1Source.stage1Owned
 all_goals repeat' first
  | (with_reducible rfl)
  | (apply forget_call)
  | (apply forget_pure)
  | (apply NMB_TypedCongr.bind_congr)
  | (apply NMB_TypedCongr.ite_congr)
  | (apply NMB_TypedCongr.control_congr)
  | intro x
  | cases x
#print forget_eq
#print axioms forget_eq
end NMB_OwnedTyped
