import NJX_InitialPrologue
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJX_InitialNodes
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon)
open NJX_InitialPrologue (Selectors)
def ranges : Slice (core.ops.range.Range Usize) :=
 ⟨[⟨4#usize,25#usize⟩,⟨33#usize,57#usize⟩],by simp;scalar_tac⟩
theorem bounds : ∀ r∈ranges.val,r.start.val≤r.end.val ∧ r.end.val≤64 := by
 intro r hr
 simp [ranges] at hr
 rcases hr with rfl|rfl <;> decide
/-- Complete260prefix consumes CLOSED sum_high at the exact frozen two
ranges, then supplies every scalar/variant/cache child Result internally. -/
theorem source (s : Selectors) (v : NJX_InitialVariant.Variant)
 (hs : FIw_ArrayValue.canonical s.high) (hl : FIw_ArrayValue.canonical s.low) :
 ∃ nodes,FIq_Native.pool_v1.pair_forest_semantic_terminal.sum_high s ranges=ok nodes ∧
 Canon nodes ∧ ∃ p : NJX_InitialPrologue.Packet s v nodes,True := by
 obtain ⟨nodes,cn,hn⟩ := NHG_ExtraLeaves.sum_result s ranges bounds hs
 obtain ⟨p,hp⟩ := NJX_InitialPrologue.source s v nodes hs hl hn
 exact ⟨nodes,cn,hn,p,hp⟩
#print source
#print axioms bounds
#print axioms source
end AspisR1.NJX_InitialNodes
end
