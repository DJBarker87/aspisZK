import NDO_JFy_SumHigh
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFy_PoseidonSelectors
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeValue (Canon)
open pool_v1.pair_forest_semantic_terminal

theorem source (s : pool_v1.pair_forest_copy_terminal.Selectors)
    (hh : FIw_ArrayValue.canonical s.high) (hl : FIw_ArrayValue.canonical s.low) :
    ∃ out,poseidon_selectors s=ok out ∧ Canon out.block ∧ FIw_ArrayValue.canonical out.«local» := by
  let ranges := Array.to_slice (Array.make 1#usize [({start:=0#usize,«end»:=57#usize} : core.ops.range.Range Usize)])
  have bound : ∀ r∈ranges.val,r.start.val≤r.end.val ∧ r.end.val≤64 := by
    intro r hr
    have eq : r=({start:=0#usize,«end»:=57#usize} : core.ops.range.Range Usize) := by simpa only [ranges,Array.to_slice,Array.make,List.mem_cons,List.not_mem_nil,or_false] using hr
    subst r
    constructor <;> decide
  obtain ⟨block,call,hblock⟩ := JFy_SumHigh.source s ranges bound hh
  refine ⟨⟨block,s.low⟩,?_,hblock,hl⟩
  unfold poseidon_selectors
  change (do let q ← sum_high s ranges
             ok ({block:=q,«local»:=s.low} : state_only_poseidon.StateOnlyPoseidonSelectors))=ok _
  rw [call,bind_tc_ok]
#print axioms source
end AspisR1.JFy_PoseidonSelectors
end
