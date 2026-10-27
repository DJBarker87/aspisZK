import FJa_SelectorOnRun
import FIx_HighSum
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJa_PoseidonSelectors
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (K Canon decode)
/-- Original Poseidon selector constructor on the SAME boxed arrays; block
weight is the installed high range[0,57), local array is the actual low array. -/
theorem value (s : pool_v1.pair_forest_copy_terminal.Selectors)
    (out : state_only_poseidon.StateOnlyPoseidonSelectors)
    (hc : FIw_ArrayValue.canonical s.high) (hl : FIw_ArrayValue.canonical s.low)
    (run : pool_v1.pair_forest_semantic_terminal.poseidon_selectors s=ok out) :
    out.local=s.low ∧ FIw_ArrayValue.canonical out.local ∧ Canon out.block ∧
      decode out.block=FIx_HighSumInner.model s 57 0 0 := by
  unfold pool_v1.pair_forest_semantic_terminal.poseidon_selectors at run
  simp only [lift,bind_tc_ok] at run
  obtain ⟨q,hq,run⟩ := FIv_Map.bind_success _ _ _ run
  have same : (⟨q,s.low⟩ : state_only_poseidon.StateOnlyPoseidonSelectors)=out := Result.ok.inj run
  subst out
  have bounds : ∀ r∈(Array.to_slice (Array.make 1#usize [
      (⟨0#usize,57#usize⟩ : core.ops.range.Range Usize)])).val,
      r.start.val≤r.end.val ∧ r.end.val≤64 := by
    intro r hr
    simp only [Array.to_slice,Array.make,List.mem_cons,List.not_mem_nil,or_false] at hr
    subst r
    decide
  have v := FIx_HighSum.value s _ q bounds hc hq
  refine ⟨rfl,hl,v.1,?_⟩
  simpa only [FIx_HighSumOuter.ranges,Array.to_slice,Array.make] using v.2
#print axioms value
end AspisR1.FJa_PoseidonSelectors
end
