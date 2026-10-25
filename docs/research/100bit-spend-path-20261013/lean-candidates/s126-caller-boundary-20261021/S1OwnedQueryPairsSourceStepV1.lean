import S1OwnedQueryBlockSourceV1
import S1OwnedQueryPairsStepModelV1
set_option autoImplicit false
namespace AspisS1OwnedQueryPairs.Model
open Aeneas Aeneas.Std Result

theorem step_source (s : OwnedScan) (state : Block) (k : Usize)
    (blocks advances : Blocks) (bound : k.val<8) (valid : Valid s) :
    ∃ (after : OwnedScan) (next : Block) (stop : Bool),
      pairs_step s state k blocks advances=ok (after,next,stop) ∧ Valid after ∧
      Query31ModelScanCall.modelScanFn Query31ConcreteWordsDriverChain.actualQueryWords
        (project s) (atBlock blocks k bound)=ok (stop,project after) ∧
      next=(if stop then atBlock advances k bound else state) := by
  obtain ⟨sf,stop,called,model,validFinal⟩ :=
    AspisS1OwnedQueryBlock.Meaning.block_source_total (project s) (atBlock blocks k bound)
      valid.1 valid.2
  dsimp only [project] at called
  let after : OwnedScan := {accepted:=sf.accepted,accepted_len:=sf.accepted_len,draws:=sf.draws}
  have validAfter : Valid after := ⟨validFinal.1,validFinal.2.1⟩
  have modelAfter : Query31ModelScanCall.modelScanFn Query31ConcreteWordsDriverChain.actualQueryWords
      (project s) (atBlock blocks k bound)=ok (stop,project after) := model
  cases stop with
  | true =>
    refine ⟨after,atBlock advances k bound,true,?_,validAfter,modelAfter,rfl⟩
    unfold pairs_step
    rw [atBlock_call blocks k bound]
    simp only [bind_tc_ok]
    rw [called]
    simp only [AspisS1OwnedQueryBlock.Meaning.pack,bind_tc_ok,if_true]
    rw [atBlock_call advances k bound]
    rfl
  | false =>
    refine ⟨after,state,false,?_,validAfter,modelAfter,rfl⟩
    unfold pairs_step
    rw [atBlock_call blocks k bound]
    simp only [bind_tc_ok]
    rw [called]
    rfl


#print axioms step_source
end AspisS1OwnedQueryPairs.Model
