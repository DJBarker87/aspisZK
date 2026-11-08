import NMS_Effect241
set_option autoImplicit false
noncomputable section
namespace NMX_R8_OldFactor241
open Aeneas Aeneas.Std Result AdapterRw NMS_Effect241
variable {M : Type → Type} [Monad M] [MonadLift Result M]
abbrev Reply := core.result.Result Unit solana_program_error.ProgramError
def afterEncode (ops : Ops) (effects : Effects M)
 (val : r1_pool_adapter.ValidatedAsqa) (val1 val2 : Slice U8)
 (proof_start val3 : Usize) (val4 : Array U8 1880#usize) : M Reply := do
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
       val1 { start := proof_start, «end» := val3 }
   let o2 ← (observer ops)
   let r6 ←
     effects.op11
       (SolanaDigest.Insts.Aspis_coreDigestDigest32 ops) s2 s3 val2
       () o2
   let r7 ←
     NMS_Effect241.mapError r6 effects.op44
   let cf5 ← core.result.Result.Insts.CoreOpsTry.branch r7
   match cf5 with
   | core.ops.control_flow.ControlFlow.Continue _ =>
     effects.op53 val.statement
   | core.ops.control_flow.ControlFlow.Break residual =>
     core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
       Unit (core.convert.FromSame
       solana_program_error.ProgramError) residual

def afterReads (ops : Ops) (effects : Effects M)
 (val : r1_pool_adapter.ValidatedAsqa) (val1 val2 : Slice U8) : M Reply := do
 let proof_start ←
   (aspis_statement.pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES ops)
 let o1 ← lift (Usize.checked_add proof_start val.proof_length)
 let r3 ←
   core.option.Option.ok_or o1
     solana_program_error.ProgramError.InvalidAccountData
 let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r3
 match cf3 with
 | core.ops.control_flow.ControlFlow.Continue val3 =>
   let i1 := Slice.len val1
   if i1 != val3
   then
     ok (core.result.Result.Err
       solana_program_error.ProgramError.InvalidAccountData)
   else
     let r4 ←
       effects.op22
         val.statement
     let r5 ←
       core.result.Result.map_err
         r1_pool_adapter.owned.stage2_owned.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestTerminalFormatErrorV1ProgramError
         r4 ()
     let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r5
     match cf4 with
     | core.ops.control_flow.ControlFlow.Continue val4 =>
       afterEncode ops effects val val1 val2 proof_start val3 val4
     | core.ops.control_flow.ControlFlow.Break residual =>
       core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
         Unit (core.convert.FromSame
         solana_program_error.ProgramError) residual
 | core.ops.control_flow.ControlFlow.Break residual =>
   core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
     Unit (core.convert.FromSame solana_program_error.ProgramError)
     residual

def afterValidate (ops : Ops) (effects : Effects M)
 (val : r1_pool_adapter.ValidatedAsqa) (accounts : Slice r1_pool_adapter.owned.OwnedAccount) : M Reply := do
 let oa ← Slice.index_usize accounts 0#usize
 let r1 ← effects.data oa
 let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
 match cf1 with
 | core.ops.control_flow.ControlFlow.Continue val1 =>
   let oa1 ← Slice.index_usize accounts 6#usize
   let r2 ← effects.data oa1
   let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
   match cf2 with
   | core.ops.control_flow.ControlFlow.Continue val2 =>
     afterReads ops effects val val1 val2
   | core.ops.control_flow.ControlFlow.Break residual =>
     core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
       Unit (core.convert.FromSame solana_program_error.ProgramError)
       residual
 | core.ops.control_flow.ControlFlow.Break residual =>
   core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
     Unit (core.convert.FromSame solana_program_error.ProgramError)
     residual

def head (ops : Ops) (effects : Effects M)
  (program_id : solana_pubkey.Pubkey)
  (accounts : Slice r1_pool_adapter.owned.OwnedAccount) (data : Slice Std.U8)
  (current_slot : core.result.Result Std.U64 solana_program_error.ProgramError)
  :
  M (core.result.Result Unit solana_program_error.ProgramError)
  := do
  let i := Slice.len accounts
  if i != 7#usize
  then
    ok (core.result.Result.Err
      solana_program_error.ProgramError.InvalidInstructionData)
  else
    let o ←
      core.slice.Slice.get (core.slice.index.SliceIndexRangeToUsizeSlice
        Std.U8) data { «end» := 4#usize }
    let a ←
      (pure aspis_statement.pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_MAGIC : Result (Array U8 4#usize))
    let s ←
      core.array.Array.index (core.ops.index.IndexSlice
        (core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice ops
        Std.U8)) a ()
    let b ←
      core.cmp.PartialEq.ne.trait_default
        (core.option.Option.Insts.CoreCmpPartialEqOption ops
        (core.cmp.PartialEqShared (Slice.Insts.CoreCmpPartialEqSlice
        core.cmp.PartialEqU8))) o (some s)
    if b
    then
      ok (core.result.Result.Err
        solana_program_error.ProgramError.InvalidInstructionData)
    else
      let r ←
        effects.validate program_id accounts data
          current_slot
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r
      match cf with
      | core.ops.control_flow.ControlFlow.Continue val =>
        afterValidate ops effects val accounts
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          Unit (core.convert.FromSame solana_program_error.ProgramError)
          residual


theorem source (ops : Ops) (effects : Effects M)
 (p : solana_pubkey.Pubkey) (accounts : Slice r1_pool_adapter.owned.OwnedAccount)
 (data : Slice U8) (slot : core.result.Result U64 solana_program_error.ProgramError) :
 head ops effects p accounts data slot = NMS_Effect241.stage2 ops effects p accounts data slot := by
 unfold head afterValidate afterReads afterEncode NMS_Effect241.stage2
 rfl
#print axioms source
end NMX_R8_OldFactor241
end
