import NMT_345BoundsFrames
set_option autoImplicit false
noncomputable section
namespace NMT_345
open Aeneas Aeneas.Std Result NMT_stage1_owned
def afterLength {W : Type} (c : Calls) (parent : HasLength W) : Result Ret := do
 let proof_start ←
   c.c8
 let o ←
   lift (Usize.checked_add proof_start parent.proofLength)
 let r13 ←
   core.option.Option.ok_or o
     solana_program_error.ProgramError.InvalidAccountData
 let cf11 ←
   core.result.Result.Insts.CoreOpsTry.branch r13
 match cf11 with
 | core.ops.control_flow.ControlFlow.Continue val5
   =>
   let i1 := Slice.len parent.proofData
   if i1 != val5
   then
     ok (core.result.Result.Err
       solana_program_error.ProgramError.InvalidAccountData)
   else
     let s ←
       core.slice.index.Slice.index
         (core.slice.index.SliceIndexRangeToUsizeSlice
         Std.U8) parent.proofData { «end» := proof_start }
     let b1 ←
       c.c0
         core.cmp.PartialEqU8 s parent.candidate
     if b1
     then
       ok (core.result.Result.Err
         solana_program_error.ProgramError.InvalidAccountData)
     else
       let i2 ←
         lift (Std.Usize.wrapping_add proof_start
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
             { start := proof_start, «end» := val5
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
 | core.ops.control_flow.ControlFlow.Break residual
   =>
   core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
     (alloc.vec.Vec Std.U8) (core.convert.FromSame
     solana_program_error.ProgramError) residual
end NMT_345
