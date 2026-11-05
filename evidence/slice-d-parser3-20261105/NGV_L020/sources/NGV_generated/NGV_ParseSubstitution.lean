import NGV_Validator
import NGV_Monad
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NGV_ParseSubstitution
open AspisR1PrefixAggregateParser
/-- Same parser and original borrowed payload; only the child reply changes. -/
theorem congr (row : U8) (record : Slice U8)
 (left right : U8 → Slice U8 → Result (core.result.Result Unit r1_wire.Error))
 (law : ∀ payload, core.slice.index.Slice.index
   (core.slice.index.SliceIndexRangeFromUsizeSlice U8) record {start:=5#usize}=ok payload →
   left row payload=right row payload) :
 NGD_ParseCut.invoke left row record=NGD_ParseCut.invoke right row record := by
 unfold NGD_ParseCut.invoke
 apply NGV_Monad.bind_congr (r:=r1_wire.row_shape row)
 intro o
 apply NGV_Monad.bind_congr (r:=core.option.Option.ok_or o r1_wire.Error.InvalidRow)
 intro r
 apply NGV_Monad.bind_congr (r:=core.result.Result.Insts.CoreOpsTry.branch r)
 intro cf
 cases cf with
 | Break residual => rfl
 | Continue pair =>
   rcases pair with ⟨tag,size⟩
   apply NGV_Monad.bind_congr (r:=5#usize+size)
   intro total
   split
   · rfl
   · apply NGV_Monad.bind_congr (r:=Slice.index_usize record 0#usize)
     intro actualTag
     split
     · rfl
     · apply NGV_Monad.bind_congr (r:=Slice.index_usize record 1#usize)
       intro b0
       apply NGV_Monad.bind_congr (r:=Slice.index_usize record 2#usize)
       intro b1
       apply NGV_Monad.bind_congr (r:=Slice.index_usize record 3#usize)
       intro b2
       apply NGV_Monad.bind_congr (r:=Slice.index_usize record 4#usize)
       intro b3
       simp only [lift,bind_tc_ok]
       split
       · rfl
       · apply NGV_Monad.bind_congr_on (r:=core.slice.index.Slice.index
           (core.slice.index.SliceIndexRangeFromUsizeSlice U8) record {start:=5#usize})
         intro payload original
         rw [law payload original]
#print axioms congr
end NGV_ParseSubstitution
