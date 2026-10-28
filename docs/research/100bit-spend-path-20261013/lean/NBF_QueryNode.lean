import NBF_Node
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace NBF_QueryNode
open AspisR1 AspisR1Stage2 Port3_NativeQueryBody
open Port3_PushFrame (bind_success)
private theorem guard {T : Type} (bad : Bool)
 (tail : Result (core.result.Result T verifier.Error)) (out : T)
 (h : (if bad then ok (.Err verifier.Error.Query) else tail)=ok (.Ok out)) :
 tail=ok (.Ok out) := by cases bad <;> simp_all
/-- The reached accumulation's node bound is derived from the SAME query's
actual scalar expression. No selected node/result canonicality is assumed. -/
theorem accepted (ops : Ops) (proof : Slice U8) (p : verifier.Prepared)
 (a out : verifier.Accumulator) (g : Array Stage2E 29#usize)
 (geometry : verifier.QueryGeometry) (b bout : verifier.BatchedWeights)
 (run : verifier.candidate.query_values (NBF_Accumulate.install ops)
   proof p a g none geometry b=ok (.Ok (out,bout))) :
 ∃ (node : U32) (line : Stage2E), node.val<2^31-1 ∧
 verifier.accumulate_batched_with_node (NBF_Accumulate.install ops)
   p a node line b=ok (out,bout) := by
 unfold verifier.candidate.query_values at run
 iterate 28 obtain ⟨x,hx,run⟩ := bind_success _ _ _ run
 have run := guard _ _ _ run
 obtain ⟨alpha,halpha,run⟩ := bind_success _ _ _ run
 obtain ⟨line,hline,run⟩ := bind_success _ _ _ run
 iterate 3 obtain ⟨x,hx,run⟩ := bind_success _ _ _ run
 obtain ⟨offset,hoffset,run⟩ := bind_success _ _ _ run
 obtain ⟨z,hz,run⟩ := bind_success _ _ _ run
 obtain ⟨square,hsquare,run⟩ := bind_success _ _ _ run
 obtain ⟨doubled,hdoubled,run⟩ := bind_success _ _ _ run
 obtain ⟨one,hone,run⟩ := bind_success _ _ _ run
 obtain ⟨node,hnode,run⟩ := bind_success _ _ _ run
 obtain ⟨pair,haccum,run⟩ := bind_success _ _ _ run
 rcases pair with ⟨a1,b1⟩
 obtain ⟨mark,hmark,run⟩ := bind_success _ _ _ run
 cases Result.ok.inj run
 have expression : NBF_Node.source ops z=ok node := by
   simp only [NBF_Node.source,hsquare,hdoubled,hone,hnode,bind_tc_ok]
 obtain ⟨actual,ha,hc⟩ := NBF_Node.total_canonical ops z
 have same := Result.ok.inj (ha.symm.trans expression)
 subst actual
 exact ⟨node,line,hc,haccum⟩
#print axioms guard
#print axioms accepted
end NBF_QueryNode
