import NMT_345TailFrames
set_option autoImplicit false
noncomputable section
namespace NMT_345
open Aeneas Aeneas.Std Result NMT_stage1_owned
def tailSplitCast {W : Type} (c : Calls) (parent : HasSplitByte W) : Result Ret := do
 let i6 ← lift (UScalar.cast .Usize parent.splitByte)
 let r14 ← c.c11 parent.semanticPublic parent.publicData parent.proofSlice i6
 let cf12 ←
   core.result.Result.Insts.CoreOpsTry.branch
     r14
 match cf12 with
 |
   core.ops.control_flow.ControlFlow.Continue
   val6 =>
   let i7 := alloc.vec.Vec.len val6
   let i8 := Slice.len parent.checkpointData
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
end NMT_345
