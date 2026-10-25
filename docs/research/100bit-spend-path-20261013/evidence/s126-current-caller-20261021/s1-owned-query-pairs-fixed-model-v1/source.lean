import S1OwnedQueryPairsIndexModelV1
import S1OwnedQueryPairsFinishModelV1
set_option autoImplicit false
namespace AspisS1OwnedQueryPairs.Model
open Aeneas Aeneas.Std Result
open AspisV8R19.SourceDuplexStep AspisV8R19.Q22WordScan AspisV8R19.SqueezeOracleBridge

/-- TOTAL source-reference driver to the fixed eight-pair model. The actual
full final scanner state and selected bytes are retained even on rejection;
all native error fields are fixed by the same source finisher. No independent
scan/driver success, default-state law, or scanner-model hypothesis remains. -/
theorem reference_total_fixed (blocks advances : Blocks) (fallback : State) :
    ∃ (sf : OwnedScan) (selected : Block),
      pairs_reference blocks advances=ok (finishValue sf selected) ∧
      walk allIndices initial (atBlock advances 7#usize (by decide)) blocks advances=
        ok (sf,selected) ∧ Valid sf ∧
      R0C.V3.Q22.scanOut 8 R0C.V3.Q22.q0 (blocks.val.map decodeState)
        (advances.val.map decodeState) fallback=(finish (qState sf),decodeState selected) ∧
      ResultMeaning (finishValue sf selected)
        (R0C.V3.Q22.scanOut 8 R0C.V3.Q22.q0 (blocks.val.map decodeState)
          (advances.val.map decodeState) fallback) := by
  obtain ⟨sf,selected,called,valid,model⟩ :=
    walk_model allIndices initial (atBlock advances 7#usize (by decide)) blocks advances initial_valid
  have source : pairs_reference blocks advances=ok (finishValue sf selected) := by
    rw [reference_eq_drive,atBlock_call advances 7#usize (by decide)]
    simp only [bind_tc_ok]
    unfold drive
    rw [called]
    simp only [bind_tc_ok]
    exact finish_eq sf selected
  rw [initial_q0] at model
  have composed := sourcePairs_eq_pairsRun (pairsOf allIndices blocks advances) R0C.V3.Q22.q0 fallback
  rw [lastAdvance_all] at composed
  have pairModel := composed.symm.trans model
  have selectedModel := AspisR1.R4Transport2ScanComposition.eight_pairs_selected
    (pairsOf allIndices blocks advances) fallback (pairsOf_all_length blocks advances)
  rw [pairsOf_all_blocks,pairsOf_all_advances] at selectedModel
  have fixed : R0C.V3.Q22.scanOut 8 R0C.V3.Q22.q0 (blocks.val.map decodeState)
      (advances.val.map decodeState) fallback=(finish (qState sf),decodeState selected) :=
    selectedModel.symm.trans pairModel
  refine ⟨sf,selected,source,called,valid,fixed,?_⟩
  rw [fixed]
  exact finish_meaning sf selected valid

#print axioms reference_total_fixed
end AspisS1OwnedQueryPairs.Model
