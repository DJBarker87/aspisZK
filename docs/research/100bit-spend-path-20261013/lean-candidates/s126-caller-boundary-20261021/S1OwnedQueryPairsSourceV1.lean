import S1OwnedQueryPairsSourceRunV1
set_option autoImplicit false
namespace AspisS1OwnedQueryPairs.Model
open Aeneas Aeneas.Std Result

/-- FULL Result equality to the query decoder already installed in preparation.
No successful execution, scan law, or model-correctness premise remains. -/
theorem reference_eq_source (blocks advances : Blocks) :
    AspisR1Query31Transcript.queries_from_pairs_with_scan
      (Query31ModelScanCall.modelScanFn Query31ConcreteWordsDriverChain.actualQueryWords)
      (project initial) blocks advances=adapt (pairs_reference blocks advances) := by
  have run := sourceTail_eq_drive allIndices initial
    (atBlock advances 7#usize (by decide)) blocks advances initial_valid
  rw [sourceTail_all,lastBlock_all] at run
  rw [reference_eq_drive,atBlock_call advances 7#usize (by decide)]
  simp only [bind_tc_ok]
  exact run

#print axioms reference_eq_source
end AspisS1OwnedQueryPairs.Model
