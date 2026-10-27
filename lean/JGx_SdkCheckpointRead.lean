import JGx_SdkProofRead
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGx_SdkCheckpointRead
open Aeneas Aeneas.Std Result
open _root_.AdapterRw

def afterCheckpoint (ops : Ops) (validated : r1_pool_adapter.ValidatedAsqa)
    (rawProof checkpoint : Slice U8) : Result (core.result.Result Unit solana_program_error.ProgramError) := do
  let proof_start ←
    (aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES ops)
  let o1 ← lift (Usize.checked_add proof_start validated.proof_length)
  let r3 ←
    core.option.Option.ok_or o1
      solana_program_error.ProgramError.InvalidAccountData
  let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r3
  match cf3 with
  | core.ops.control_flow.ControlFlow.Continue val3 =>
    let i1 := Slice.len rawProof
    if i1 != val3
    then
      ok (core.result.Result.Err
        solana_program_error.ProgramError.InvalidAccountData)
    else
      let r4 ←
        ops.op22
          validated.statement
      let r5 ←
        core.result.Result.map_err
          r1_pool_adapter.owned.stage2_owned.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestTerminalFormatErrorV1ProgramError
          r4 ()
      let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r5
      match cf4 with
      | core.ops.control_flow.ControlFlow.Continue val4 =>
        let s1 ← lift (Array.to_slice val4)
        let i2 := Slice.len s1
        let i3 ←
          (aspis_statement.pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_BYTES ops)
        if i2 != i3
        then
          ok (core.result.Result.Err
            solana_program_error.ProgramError.InvalidInstructionData)
        else
          let s2 ← lift (Array.to_slice val4)
          let s3 ←
            core.slice.index.Slice.index
              (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)
              rawProof { start := proof_start, «end» := val3 }
          let o2 ← (observer ops)
          let r6 ←
            ops.op11
              (SolanaDigest.Insts.Aspis_coreDigestDigest32 ops) s2 s3 checkpoint
              () o2
          let r7 ←
            core.result.Result.map_err (BuiltinFnOnce
              aspis_r1_cost_probe.verifier.Error
              solana_program_error.ProgramError) r6 (ops.op44)
          let cf5 ← core.result.Result.Insts.CoreOpsTry.branch r7
          match cf5 with
          | core.ops.control_flow.ControlFlow.Continue _ =>
            ops.op53 validated.statement
          | core.ops.control_flow.ControlFlow.Break residual =>
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              Unit (core.convert.FromSame
              solana_program_error.ProgramError) residual
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          Unit (core.convert.FromSame
          solana_program_error.ProgramError) residual
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      Unit (core.convert.FromSame solana_program_error.ProgramError)
      residual

theorem source (ops : Ops) (accounts : S2W_ExtractionBoundary.Accounts)
    (validated : r1_pool_adapter.ValidatedAsqa) (rawProof checkpoint : Slice U8)
    (account : r1_pool_adapter.owned.OwnedAccount)
    (index : Slice.index_usize accounts 6#usize=ok account)
    (read : r1_pool_adapter.owned.OwnedAccount.data ops account=ok (.Ok checkpoint)) :
    JGx_SdkProofRead.afterProof ops accounts validated rawProof=afterCheckpoint ops validated rawProof checkpoint := by
  unfold JGx_SdkProofRead.afterProof
  rw [index,bind_tc_ok,read,bind_tc_ok]
  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
  rfl
#print axioms source
end AspisR1.JGx_SdkCheckpointRead
end
