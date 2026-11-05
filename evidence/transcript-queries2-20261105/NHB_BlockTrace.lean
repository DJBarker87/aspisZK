import NHB_WordTrace
set_option autoImplicit false
namespace AspisR1.NHB_BlockTrace
open Aeneas Aeneas.Std Result
open NGQ_SamplerDriver
open Query31ExplicitListLoop
abbrev Scan := NGQ_SamplerPacket.Scan

theorem block_source (block : Bytes32) (words : Array U32 8#usize)
    (s final : State) (last : Nat) (pending : Option Bool)
    (decode : Query31ConcreteWordsDriverChain.actualQueryWords block=ok words)
    (edges : NHB_WordTrace.Trace 0 words.val s final last pending) :
    Scan s block=ok (optionStop pending,final) ∧ last≤8 := by
  refine ⟨NGQ_SamplerNative.source block words s final pending decode
    (NHB_WordTrace.association edges),?_⟩
  have bound := (NHB_WordTrace.cursor_bound edges).2
  have size : words.val.length=8 := words.property
  simpa only [Nat.zero_add,size] using bound

/-- Source-order blocks. Stop is tested by the SAME word loop. At a block end
pending=some false, so the following block/advance is selected if its first
word observes fullness. No early post-word success check is inserted. -/
inductive Trace (advances : Blocks) : List (Bytes32×Usize) → State → Out → Prop where
 | exhausted (s : State) (out : Out)
     (finish : AspisR1Query31Transcript.finishAdvance advances 7#usize s=ok out) :
     Trace advances [] s out
 | stopped (block : Bytes32) (index : Usize) (tail : List (Bytes32×Usize))
     (s next : State) (out : Out) (words : Array U32 8#usize) (last : Nat) (pending : Option Bool)
     (decode : Query31ConcreteWordsDriverChain.actualQueryWords block=ok words)
     (edges : NHB_WordTrace.Trace 0 words.val s next last pending)
     (stop : optionStop pending=true)
     (finish : AspisR1Query31Transcript.finishAdvance advances index next=ok out) :
     Trace advances ((block,index)::tail) s out
 | continuing (block : Bytes32) (index : Usize) (tail : List (Bytes32×Usize))
     (s next : State) (out : Out) (words : Array U32 8#usize) (last : Nat) (pending : Option Bool)
     (decode : Query31ConcreteWordsDriverChain.actualQueryWords block=ok words)
     (edges : NHB_WordTrace.Trace 0 words.val s next last pending)
     (stop : optionStop pending=false)
     (rest : Trace advances tail next out) :
     Trace advances ((block,index)::tail) s out

theorem walk_source {advances : Blocks} {inputs : List (Bytes32×Usize)}
    {s : State} {out : Out} (trace : Trace advances inputs s out) :
    NGQ_SamplerDriver.walk Scan advances 7#usize inputs s=ok out := by
  induction trace with
  | exhausted s out finish => exact finish
  | stopped block index tail s next out words last pending decode edges stop finish =>
    have scan := (block_source block words s next last pending decode edges).1
    simp only [NGQ_SamplerDriver.walk,scan,bind_tc_ok]
    dsimp! only
    simpa only [stop,if_true] using finish
  | continuing block index tail s next out words last pending decode edges stop rest ih =>
    have scan := (block_source block words s next last pending decode edges).1
    simp only [NGQ_SamplerDriver.walk,scan,bind_tc_ok]
    dsimp! only
    simpa only [stop,Bool.false_eq_true,if_false] using ih

#print axioms block_source
#print axioms walk_source
end AspisR1.NHB_BlockTrace
