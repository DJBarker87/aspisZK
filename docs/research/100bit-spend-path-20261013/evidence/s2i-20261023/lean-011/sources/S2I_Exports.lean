import S2I_ClearChild
import S2I_StageJoin
import S2I_SessionAStatements

/-! Focused compatible union, not a coherent frozen-release replay. -/
#print axioms AspisR1.S2I.ReturnData.clear_contract
#print axioms AspisR1.S2I.ReturnData.before_asq8
#print axioms AspisR1.S2I.ReturnData.rejected_asq8
#print axioms AspisR1.S2I.ReturnData.nonempty_event
#print axioms AspisR1.S2I.ClearChild.reached_asq8
#print axioms AspisR1.S2I.StageJoin.ordered_checkpoint_batches
#print axioms AspisR1.S2I.StageJoin.second_batch_stage
#print axioms AspisR1.S2I.StageJoin.same_stored_scan
