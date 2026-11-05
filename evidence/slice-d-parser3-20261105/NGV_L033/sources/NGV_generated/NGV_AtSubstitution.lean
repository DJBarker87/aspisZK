import NGV_ParsePacket
import NGD_AtReference
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NGV_AtSubstitution
open AspisR1PrefixAggregateParser
/-- Reached-child substitution on the SAME original get window. Every get,
error and borrowed-return branch remains in the caller. -/
theorem congr (bytes : Slice U8) (row tag : U8) (offset size length finish : Usize)
 (left right : U8 → Slice U8 → Result (core.result.Result (Slice U8) r1_wire.Error))
 (shape : r1_wire.row_shape row=ok (some (tag,size)))
 (lengthAdd : 5#usize+size=ok length) (endAdd : offset+length=ok finish)
 (law : ∀ framed,core.slice.Slice.get (core.slice.index.SliceIndexRangeUsizeSlice U8)
   bytes {start:=offset,«end»:=finish}=ok (some framed) →left row framed=right row framed) :
 NGD_AtCut.invoke left bytes row offset=NGD_AtCut.invoke right bytes row offset := by
 unfold NGD_AtCut.invoke
 simp only [shape,core.option.Option.unwrap,ofOption,bind_tc_ok,lengthAdd,endAdd]
 try dsimp only
 simp only [lengthAdd,endAdd,bind_tc_ok]
 apply NGV_Monad.bind_congr_on (r:=core.slice.Slice.get (core.slice.index.SliceIndexRangeUsizeSlice U8)
   bytes {start:=offset,«end»:=finish})
 intro value original
 cases value with
 | none => rfl
 | some framed =>
   simp only [core.option.Option.ok_or,bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch]
   rw [law framed original]
#print axioms congr
end NGV_AtSubstitution
