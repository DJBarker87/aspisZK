import S1OwnedQueryPairsSourceFinishV1
import S1OwnedQueryPairsIndexModelV1
set_option autoImplicit false
namespace AspisS1OwnedQueryPairs.Model
open Aeneas Aeneas.Std Result
abbrev SourceScan := Query31ExplicitScanBody.CurrentScan

def sourceTail : List (Fin 8) → SourceScan → Block → Blocks → Blocks → Result OldResult
  | [],s,state,_,_ => adapt (pairs_finish ⟨s.accepted,s.accepted_len,s.draws⟩ state)
  | [k],s,_,blocks,advances => do
    let block ← Array.index_usize blocks (index k)
    let (_,sf) ← Query31ModelScanCall.modelScanFn Query31ConcreteWordsDriverChain.actualQueryWords s block
    AspisR1Query31Transcript.finishAdvance advances (index k) sf
  | k::j::ks,s,state,blocks,advances => do
    let block ← Array.index_usize blocks (index k)
    let (stop,sf) ← Query31ModelScanCall.modelScanFn Query31ConcreteWordsDriverChain.actualQueryWords s block
    if stop then AspisR1Query31Transcript.finishAdvance advances (index k) sf
    else sourceTail (j::ks) sf state blocks advances

def lastBlock : List (Fin 8) → Blocks → Block → Block
  | [],_,fallback => fallback
  | [k],advances,_ => atBlock advances (index k) (index_bound k)
  | _::j::ks,advances,fallback => lastBlock (j::ks) advances fallback

/-- The exact finite source driver is represented by this suffix traversal;
all source finish/error branches remain in the definition. -/
theorem sourceTail_all (s : SourceScan) (fallback : Block) (blocks advances : Blocks) :
    sourceTail allIndices s fallback blocks advances=
      AspisR1Query31Transcript.queries_from_pairs_with_scan
        (Query31ModelScanCall.modelScanFn Query31ConcreteWordsDriverChain.actualQueryWords)
        s blocks advances := by
  rw [allIndices_list]
  rfl

theorem lastBlock_all (advances : Blocks) (fallback : Block) :
    lastBlock allIndices advances fallback=atBlock advances 7#usize (by decide) := by
  rw [allIndices_list]
  rfl

#print axioms sourceTail_all
#print axioms lastBlock_all
end AspisS1OwnedQueryPairs.Model
