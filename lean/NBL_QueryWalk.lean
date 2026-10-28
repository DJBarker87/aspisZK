import NBA_QueryNative
import Query31ConcreteMaterializedSchedule
set_option autoImplicit false
namespace AspisR1.NBL_QueryWalk
open Aeneas Aeneas.Std Result
open AspisR1Query31Transcript Query31ExplicitListLoop Query31ExplicitScanBody
open NBA_QueryDriver
abbrev Pairs := List (Bytes32×Usize)

/-- Full first-stop trace on ONE state carrier. Each scan is constructed
from native word/decode/one-step relations; only the reached local finish
is observed. No successful decoder or whole-driver equality is a premise. -/
inductive Trace (advances : Blocks) (fallback : Usize) : Pairs → State → Result Out → Prop where
  | exhausted (s : State) (result : Result Out)
      (finish : finishAdvance advances fallback s=result) : Trace advances fallback [] s result
  | stopped (block : Bytes32) (index : Usize) (rest : Pairs) (s final : State)
      (words : Array U32 8#usize) (pending : Option Bool) (result : Result Out)
      (decode : Query31ConcreteWordsDriverChain.actualQueryWords block=ok words)
      (scan : NBA_QueryTrace.Trace words.val s final pending)
      (stop : optionStop pending=true)
      (finish : finishAdvance advances index final=result) :
      Trace advances fallback ((block,index)::rest) s result
  | continuing (block : Bytes32) (index : Usize) (rest : Pairs) (s next : State)
      (words : Array U32 8#usize) (pending : Option Bool) (result : Result Out)
      (decode : Query31ConcreteWordsDriverChain.actualQueryWords block=ok words)
      (scan : NBA_QueryTrace.Trace words.val s next pending)
      (stop : optionStop pending=false) (tail : Trace advances fallback rest next result) :
      Trace advances fallback ((block,index)::rest) s result

theorem source (advances : Blocks) (fallback : Usize) {pairs : Pairs} {s : State} {result : Result Out}
    (trace : Trace advances fallback pairs s result) :
    walk (Query31ModelScanCall.modelScanFn Query31ConcreteWordsDriverChain.actualQueryWords)
      advances fallback pairs s=result := by
  induction trace with
  | exhausted s result finish => exact finish
  | stopped block index rest s final words pending result decode scan stop finish =>
    rw [walk,NBA_QueryNative.source block words s final pending decode scan,bind_tc_ok]
    simp only [stop,↓reduceIte]
    exact finish
  | continuing block index rest s next words pending result decode scan stop tail ih =>
    rw [walk,NBA_QueryNative.source block words s next pending decode scan,bind_tc_ok]
    simp only [stop,Bool.false_eq_true,↓reduceIte]
    exact ih

/-- Model-trace existence on every bounded prestate, including the exact first
rejection/fail/div finish. This is not a Rust interpreter existence theorem. -/
theorem construct (advances : Blocks) (fallback : Usize) (pairs : Pairs) (s : State)
    (good : validState s) : ∃ result,Trace advances fallback pairs s result := by
  induction pairs generalizing s with
  | nil => exact ⟨finishAdvance advances fallback s,.exhausted s _ rfl⟩
  | cons pair rest ih =>
    rcases pair with ⟨block,index⟩
    obtain ⟨words,next,pending,decode,scan,valid,call⟩ := NBA_QueryNative.construct block s good
    cases stop : optionStop pending with
    | true => exact ⟨finishAdvance advances index next,.stopped block index rest s next words pending _ decode scan stop rfl⟩
    | false =>
      obtain ⟨result,tail⟩ := ih next valid
      exact ⟨result,.continuing block index rest s next words pending result decode scan stop tail⟩

theorem decoder (blocks advances : Blocks) (s : State) (result : Result Out)
    (trace : Trace advances 7#usize
      (blocks.val.zip [0#usize,1#usize,2#usize,3#usize,4#usize,5#usize,6#usize,7#usize]) s result) :
    Query31ConcreteMaterializedSchedule.actualConcreteDecode s blocks advances=
      Query31ConcreteMaterializedSchedule.adaptScanResult result := by
  unfold Query31ConcreteMaterializedSchedule.actualConcreteDecode
  rw [NBA_QueryDriver.source,source advances 7#usize trace]

#print axioms source
#print axioms construct
#print axioms decoder
end AspisR1.NBL_QueryWalk
