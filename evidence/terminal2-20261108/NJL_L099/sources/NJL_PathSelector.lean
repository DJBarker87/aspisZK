import NJL_PathAssociation
import NIH_SelectorRow
import NHG_ExtraLeaves
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJL_PathSelector
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon)
abbrev Selectors := FIq_Native.pool_v1.pair_forest_copy_terminal.Selectors
def ranges : Slice (core.ops.range.Range Usize) := ⟨[⟨57#usize,63#usize⟩],by simp;scalar_tac⟩
def low (s : Selectors) (i : Fin 16) : NQ := NJB_ArrayCarrier.cell s.low i
def reference (s : Selectors) : Result NQ := do
 let high ← FIq_Native.pool_v1.pair_forest_semantic_terminal.sum_high s ranges
 let a ← FIq_Native.field.QM31.add (low s 1) (low s 5)
 let b ← FIq_Native.field.QM31.add a (low s 9)
 let c ← FIq_Native.field.QM31.add b (low s 13)
 FIq_Native.field.QM31.mul high c
structure Packet (s : Selectors) where
 high : NQ
 a : NQ
 b : NQ
 c : NQ
 selector : NQ
 high_call : FIq_Native.pool_v1.pair_forest_semantic_terminal.sum_high s ranges=ok high
 a_call : FIq_Native.field.QM31.add (low s 1) (low s 5)=ok a
 b_call : FIq_Native.field.QM31.add a (low s 9)=ok b
 c_call : FIq_Native.field.QM31.add b (low s 13)=ok c
 product_call : FIq_Native.field.QM31.mul high c=ok selector
 canonical : Canon selector
/-- CLOSED262 receives only range57..63⊂high64; all four low reads are
inside low16, three adds then SAME high*low selector actual Result. -/
theorem source (s : Selectors) (hh : FIw_ArrayValue.canonical s.high) (hl : FIw_ArrayValue.canonical s.low) :
 ∃ p : Packet s,reference s=ok p.selector := by
 have bounds : ∀ r∈ranges.val,r.start.val≤r.end.val ∧ r.end.val≤64 := by
  intro r h
  have same : r=⟨57#usize,63#usize⟩ := by simpa only [ranges,List.mem_singleton] using h
  subst r;decide
 obtain ⟨high,ch,hhv⟩ := NHG_ExtraLeaves.sum_result s ranges bounds hh
 have lc : ∀ i,Canon (low s i) := NJB_ArrayCarrier.canonical_cell s.low hl
 obtain ⟨a,ca,ha,_⟩ := NJB_StubLaws.qm_add (low s 1) (low s 5) (lc 1) (lc 5)
 obtain ⟨b,cb,hb,_⟩ := NJB_StubLaws.qm_add a (low s 9) ha (lc 9)
 obtain ⟨c,cc,hc,_⟩ := NJB_StubLaws.qm_add b (low s 13) hb (lc 13)
 obtain ⟨selector,cs,hs,_⟩ := NJB_StubLaws.qm_mul high c hhv hc
 refine ⟨⟨high,a,b,c,selector,ch,ca,cb,cc,cs,hs⟩,?_⟩
 simp only [reference,ch,ca,cb,cc,cs,bind_tc_ok]
#print Packet
#print source
#print axioms source
end AspisR1.NJL_PathSelector
end
