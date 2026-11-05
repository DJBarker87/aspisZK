import NGV_ChunkCheck
import NGO_IteratorStep
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NGV_ValidatorStep
open AspisR1PrefixAggregateParser
abbrev Iter := NGO_IteratorStep.Native
theorem cut (row : U8) (iter after : Iter) (i : Usize) (bs : Slice U8)
 (next : core.iter.adapters.enumerate.IteratorEnumerate.next
   (core.iter.traits.iterator.IteratorChunksExact U8) iter=ok (some (i,bs),after)) :
 r1_wire.validate_record_fields_loop.body row iter = do
   let reply ← NGV_ChunkCheck.invoke row i bs
   match reply with
   | .Ok _ => ok (.cont after)
   | .Err e => ok (.done (.Err e)) := by
 simp only [r1_wire.validate_record_fields_loop.body,next,bind_tc_ok]
 unfold NGV_ChunkCheck.invoke
 cases run : field.wide_exact.WideExact.from_le_bytes bs with
 | fail e => simp [run]
 | div => simp [run]
 | ok value =>
   cases value <;>
    simp [run,core.option.Option.ok_or,core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      field.wide_exact.WideExact.impl.c1]
   split <;> simp_all
theorem step (row : U8) (iter after : Iter) (i : Usize) (bs : Slice U8)
 (next : core.iter.adapters.enumerate.IteratorEnumerate.next
   (core.iter.traits.iterator.IteratorChunksExact U8) iter=ok (some (i,bs),after))
 (size : bs.val.length=32) :
 r1_wire.validate_record_fields_loop.body row iter =
 ok (if NFU_Retarget.LPl_Kit_Bytes.validChunk 8 true bs.val
   then .cont after else .done (.Err (.NonCanonical row i))) := by
 rw [cut row iter after i bs next,NGV_ChunkCheck.result row i bs size]
 split <;> simp_all
#print axioms cut
#print axioms step
end NGV_ValidatorStep
