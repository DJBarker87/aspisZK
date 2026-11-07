import NMT_345Frames
set_option autoImplicit false
noncomputable section
namespace NMT_345
open Aeneas Aeneas.Std Result NMT_stage1_owned
/-- Verbatim E003 continuation at emitted Try occurrence 9; only local
captures are projected from the single complete parent state. -/
def raw09 {W : Type} (c : Calls) (parent : Candidate W) : Result Ret := do
 let r12 ←
   (r1_pool_adapter.owned.OwnedAccount.data c.c10)
     parent.proofAccount
 let cf10 ←
   core.result.Result.Insts.CoreOpsTry.branch r12
 match cf10 with
 | core.ops.control_flow.ControlFlow.Continue val4 =>
   let proof_length ←
     c.c4
   let proof_start ←
     c.c8
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
         let i3 ← Slice.index_usize val4 i2
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
               Std.U8) val4
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
 | core.ops.control_flow.ControlFlow.Break residual =>
   core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
     (alloc.vec.Vec Std.U8) (core.convert.FromSame
     solana_program_error.ProgramError) residual
end NMT_345
