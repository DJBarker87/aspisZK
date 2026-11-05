import NHK_NativeWords
set_option autoImplicit false
noncomputable section
namespace AspisR1.NHK_NativeBlocks
open Aeneas Aeneas.Std Result
open NGQ_SamplerDriver

/-- Outer cuts from the SAME arrays and scan state. The word trace contains
K053's raw observations. A stopped edge selects this index's advance; an
exhausted outer iterator retains the initial advance7. -/
inductive Cuts (advances : Blocks) : List (Bytes32×Usize) → State → Out → Prop where
 | exhausted (s : State) (out : Out)
     (finish : AspisR1Query31Transcript.finishAdvance advances 7#usize s=ok out) :
     Cuts advances [] s out
 | stopped (block : Bytes32) (index : Usize) (tail : List (Bytes32×Usize))
     (s next : State) (out : Out) (words : Array U32 8#usize) (last : Nat) (pending : Option Bool)
     (decode : Query31ConcreteWordsDriverChain.actualQueryWords block=ok words)
     (edges : NHK_NativeWords.Cuts 0 words.val s next last pending)
     (stop : Query31ExplicitListLoop.optionStop pending=true)
     (finish : AspisR1Query31Transcript.finishAdvance advances index next=ok out) :
     Cuts advances ((block,index)::tail) s out
 | continuing (block : Bytes32) (index : Usize) (tail : List (Bytes32×Usize))
     (s next : State) (out : Out) (words : Array U32 8#usize) (last : Nat) (pending : Option Bool)
     (decode : Query31ConcreteWordsDriverChain.actualQueryWords block=ok words)
     (edges : NHK_NativeWords.Cuts 0 words.val s next last pending)
     (stop : Query31ExplicitListLoop.optionStop pending=false)
     (rest : Cuts advances tail next out) :
     Cuts advances ((block,index)::tail) s out

theorem association {advances : Blocks} {inputs : List (Bytes32×Usize)} {s : State} {out : Out}
    (cuts : Cuts advances inputs s out) : NHB_BlockTrace.Trace advances inputs s out := by
  induction cuts with
  | exhausted s out finish => exact .exhausted s out finish
  | stopped block index tail s next out words last pending decode edges stop finish =>
    exact .stopped block index tail s next out words last pending decode
      (NHK_NativeWords.association edges) stop finish
  | continuing block index tail s next out words last pending decode edges stop rest ih =>
    exact .continuing block index tail s next out words last pending decode
      (NHK_NativeWords.association edges) stop ih

/-- Full Result at the observed native output, including rejection. -/
theorem sampler (blocks advances : Blocks) (out : Out)
    (cuts : Cuts advances
      (blocks.val.zip [0#usize,1#usize,2#usize,3#usize,4#usize,5#usize,6#usize,7#usize])
      NGQ_SamplerPacket.initial out) :
    NGQ_SamplerPacket.decode blocks advances=ok (NHB_Sampler.port out) ∧
    Query31ConcreteMaterializedSchedule.actualConcreteDecode
      NGQ_SamplerPacket.initial blocks advances=ok (NHB_Sampler.port out) :=
  ⟨NHB_Sampler.decode_source blocks advances out (association cuts),
   NHB_Sampler.cohort_source blocks advances out (association cuts)⟩

#print axioms association
#print axioms sampler
end AspisR1.NHK_NativeBlocks
end
