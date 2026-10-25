import S1OwnedQueryBlockSourceLoopV1
import S1QueryWordsTotalV1
set_option autoImplicit false
namespace AspisS1OwnedQueryBlock.Meaning
open Aeneas Aeneas.Std Result
open Query31ExplicitScanBody

/-- TOTAL same complete state in the concrete owned block and the existing
source-shaped decoder/Std/list-iterator interpretation. -/
theorem block_source_total (s : CurrentScan) (block : Array U8 32#usize)
    (hlen : s.accepted_len.val≤22) (hd : s.draws.val≤64) :
    ∃ (sf : CurrentScan) (stop : Bool),
      owned_block s.accepted s.accepted_len s.draws block=ok (pack sf stop) ∧
      Query31ModelScanCall.modelScanFn Query31ConcreteWordsDriverChain.actualQueryWords
        s block=ok (stop,sf) ∧ Query31ExplicitListLoop.validState sf := by
  obtain ⟨sf,stop,called,source,valid⟩ := block_loop_source 8 s block 0#usize hlen hd
    (by scalar_tac) (by scalar_tac)
  obtain ⟨words,decoded,values⟩ := AspisS1QueryWordsTotal.words_total block
  have values' : words.val=sourceWordsFrom block 0 := by
    rw [values]
    simp only [sourceWordsFrom,List.drop_zero,sampleWord]
  refine ⟨sf,stop,?_,?_,valid⟩
  · unfold owned_block
    rw [called]
    cases stop <;> rfl
  · unfold Query31ModelScanCall.modelScanFn Query31ConcreteWordsDriverChain.actualQueryWords
    rw [decoded]
    simp only [bind_tc_ok,values',source]
    cases stop <;> rfl

/-- Full Result equality. No successful source/owned decode, word callback,
scanner transition, iterator or model law is supplied as a premise. -/
theorem block_eq_source (s : CurrentScan) (block : Array U8 32#usize)
    (hlen : s.accepted_len.val≤22) (hd : s.draws.val≤64) :
    (do
      let (a,n,d,stop) ← owned_block s.accepted s.accepted_len s.draws block
      ok (stop,({accepted:=a,accepted_len:=n,draws:=d} : CurrentScan)))=
      Query31ModelScanCall.modelScanFn Query31ConcreteWordsDriverChain.actualQueryWords s block := by
  obtain ⟨sf,stop,called,source,valid⟩ := block_source_total s block hlen hd
  rw [called,source]
  rfl

#print axioms block_source_total
#print axioms block_eq_source
end AspisS1OwnedQueryBlock.Meaning
