import FIv_Arithmetic
import FIq_Native14
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIv_TerminalParts
open Aeneas Aeneas.Std Result
open FIq_Native
abbrev NQ := FIq_Native.field.QM31
abbrev Parts := NQ × Array NQ 16#usize × Array NQ 10#usize × NQ
abbrev PartError := pool_v1.pair_forest_semantic_terminal.PoolV1PairForestSemanticTerminalErrorV1
abbrev firstCallback := pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31.closure_1.Insts.CoreOpsFunctionFnOnceTupleTupleQM31ArrayQM3116ArrayQM3110QM31QM31
abbrev errorCallback := pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31.closure_2.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestSemanticTerminalErrorV1Error

theorem maps (parts : Aeneas.Std.core.result.Result Parts PartError) (out : NQ)
    (success : (do
      let first ← FIq_Native.core.result.Result.map firstCallback parts ()
      FIq_Native.core.result.Result.map_err errorCallback first ())=ok (.Ok out)) :
    ∃ c1 mask g,parts=.Ok (out,c1,mask,g) := by
  cases parts with
  | Err e =>
    simp only [FIq_Native.core.result.Result.map,FIq_Native.core.result.Result.map_err,
      firstCallback,errorCallback,
      pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31.closure_2.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestSemanticTerminalErrorV1Error,
      pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31.closure_2.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestSemanticTerminalErrorV1Error.call_once,
      bind_tc_ok] at success
    cases success
  | Ok p =>
    rcases p with ⟨q,c1,mask,g⟩
    simp only [FIq_Native.core.result.Result.map,FIq_Native.core.result.Result.map_err,
      firstCallback,errorCallback,
      pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31.closure_1.Insts.CoreOpsFunctionFnOnceTupleTupleQM31ArrayQM3116ArrayQM3110QM31QM31,
      pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31.closure_1.Insts.CoreOpsFunctionFnOnceTupleTupleQM31ArrayQM3116ArrayQM3110QM31QM31.call_once,
      bind_tc_ok] at success
    have same : q=out := Aeneas.Std.core.result.Result.Ok.inj (Result.ok.inj success)
    exact ⟨c1,mask,g,by rw [same]⟩

theorem reached (pub : pool_v1.pair_forest_semantic_terminal.r0.Public)
    (claims : Array (Array NQ 29#usize) 3#usize) (alpha : Array NQ 10#usize)
    (c : state_only_prefix.r0.Challenges) (out : NQ)
    (success : pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31 pub claims alpha c=ok (.Ok out)) :
    ∃ selected sem c1 mask g,
      FIq_Native.array_from_fn_copy 84#usize FIq_Native.field.QM31.Insts.CoreMarkerCopy
        pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
        FIq_Native.field.QM31.ZERO claims=ok selected ∧
      pool_v1.pair_forest_semantic_terminal.r0.Public.semantic pub=ok sem ∧
      pool_v1.pair_forest_semantic_terminal.terminal_parts sem selected alpha
        c.lambda c.chi c.theta c.zc c.mu=ok (.Ok (out,c1,mask,g)) := by
  unfold pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31 at success
  obtain ⟨selected,gather,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨sem,semantic,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨parts,called,success⟩ := FIv_Map.bind_success _ _ _ success
  obtain ⟨c1,mask,g,same⟩ := maps parts out success
  exact ⟨selected,sem,c1,mask,g,gather,semantic,by rw [same] at called;exact called⟩

#print axioms maps
#print axioms reached
end AspisR1.FIv_TerminalParts
end
