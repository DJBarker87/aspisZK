import JGx_SdkCheckpointRead
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGx_SdkEncoded
open Aeneas Aeneas.Std Result
open _root_.AdapterRw

def afterEncoded (ops : Ops) (validated : r1_pool_adapter.ValidatedAsqa)
    (rawProof checkpoint : Slice U8) (encoded : Array U8 1880#usize) :
    Result (core.result.Result Unit solana_program_error.ProgramError) := do
  let s1 ← lift (Array.to_slice encoded)
  let i2 := Slice.len s1
  let i3 ←
    (aspis_statement.pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_BYTES ops)
  if i2 != i3
  then
    ok (core.result.Result.Err
      solana_program_error.ProgramError.InvalidInstructionData)
  else
    let s2 ← lift (Array.to_slice encoded)
    let s3 ←
      core.slice.index.Slice.index
        (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)
        rawProof { start := 688#usize, «end» := 58295#usize }
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

#print axioms afterEncoded
end AspisR1.JGx_SdkEncoded
end
