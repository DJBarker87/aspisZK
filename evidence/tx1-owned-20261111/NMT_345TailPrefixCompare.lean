import NMT_345TailFrames
set_option autoImplicit false
noncomputable section
namespace NMT_345
open Aeneas Aeneas.Std Result NMT_stage1_owned
def tailPrefixCompare {W : Type} (c : Calls) (parent : HasPrefix W) : Result Ret := do
 let b1 ←
   c.c0
     core.cmp.PartialEqU8 parent.proofPrefix parent.candidate
 if b1
 then
   ok (core.result.Result.Err
     solana_program_error.ProgramError.InvalidAccountData)
 else
   let i2 ←
     lift (Std.Usize.wrapping_add parent.proofStart
       8#usize)
   let i3 ← Slice.index_usize parent.proofData i2
   let i4 ←
     c.c3
       aspis_r1_cost_probe.transport.Variant.S2
   if i3 != i4
   then
     ok (core.result.Result.Err
       solana_program_error.ProgramError.InvalidAccountData)
   else
     let p ←
       c.c5
         parent.statement
     let s1 ←
       core.slice.index.Slice.index
         (core.slice.index.SliceIndexRangeUsizeSlice
         Std.U8) parent.proofData
         { start := parent.proofStart, «end» := parent.proofEnd
         }
     let i5 ← Slice.index_usize parent.data 1#usize
     let i6 ← lift (UScalar.cast .Usize i5)
     let r14 ← c.c11 p parent.publicData s1 i6
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
