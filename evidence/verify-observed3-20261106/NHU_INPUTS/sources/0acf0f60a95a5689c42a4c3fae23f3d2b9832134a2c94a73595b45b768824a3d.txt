import NHG_COMBINED_IMPORT
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.NHU_PoseidonSelectors
open FIq_Native
open pool_v1.pair_forest_semantic_terminal
abbrev S := pool_v1.pair_forest_copy_terminal.Selectors
abbrev P := state_only_poseidon.StateOnlyPoseidonSelectors

def ranges : Slice (core.ops.range.Range Usize) :=
 Array.to_slice (Array.make 1#usize [⟨0#usize,57#usize⟩])

theorem bounds : ∀ r∈ranges.val,r.start.val≤r.end.val ∧ r.end.val≤64 := by
 intro r mem
 have same : r=⟨0#usize,57#usize⟩ := by simpa only [ranges,Array.to_slice,Array.make,List.mem_cons,List.not_mem_nil,or_false] using mem
 subst r
 constructor <;> decide

theorem source (s : S) : poseidon_selectors s=(do
 let block←sum_high s ranges
 ok ({block:=block,«local»:=s.low} : P)) := rfl

theorem result (s : S) (canonical : AspisR1.FIw_ArrayValue.canonical s.high) :
 ∃ out,poseidon_selectors s=ok out ∧ out.local=s.low ∧
 AspisR1.FIv_NativeValue.Canon out.block := by
 obtain ⟨block,call,canon⟩:=NHG_ExtraLeaves.sum_result s ranges bounds canonical
 refine ⟨{block:=block,«local»:=s.low},?_,rfl,canon⟩
 rw [source,call,bind_tc_ok]
#print axioms bounds
#print axioms source
#print axioms result
end AspisR1.NHU_PoseidonSelectors
