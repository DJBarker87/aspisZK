import NKI_ValueFinish
import NKI_ValueTotal
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKI_ValueAssociation
open Aeneas Aeneas.Std Result WP FIq_Native
open FIv_NativeArithmetic (NQ)
open FIw_ArrayValue (canonical)
open NKI_ValuePrefix (Openings Selectors Tail)
def reference (packed : Array NQ 24#usize) (o : Openings) (s : Selectors) : Result (Array NQ 24#usize) := do
 let t←NKI_ValuePrefix.run o s
 NKI_ValueFinish.reference packed t.openings s t.range t.selector
/-- Full233 SOURCE association at the actual33cell shared-selector/start49
and conservation/start82calls. Every returning carrier is complete24cells. -/
theorem source (packed : Array NQ 24#usize) (o : Openings) (s : Selectors)
 (hp : canonical packed) (hz : canonical o.z) (hs : canonical o.succ_z) (hx : canonical o.xor12_z)
 (hh : canonical s.high) (hl : canonical s.low) :
 ∃ (t : Tail) (middle out : Array NQ 24#usize),
 NKI_ValuePrefix.run o s=ok t ∧ t.openings=o ∧ NKI_ValueTotal.Canonical t ∧
 NJL_SharedRoot.reference packed t.range t.selector=ok middle ∧
 NKI_ValueFinish.conservation middle o s=ok out ∧ canonical middle ∧ canonical out ∧
 reference packed o s=ok out ∧ pool_v1.pair_forest_semantic_terminal.add_value_lanes packed o s=ok out := by
 obtain ⟨t,ct,ot,ht⟩ := WP.spec_imp_exists (NKI_ValueTotal.source o s hz hs hx hh hl)
 obtain ⟨weighted,after,muls,cm,trace,old,hm,vm⟩ := NJL_SharedRoot.source packed t.range t.selector hp ht.2 ht.1
 obtain ⟨out,co,ho⟩ := WP.spec_imp_exists (NKI_ValueFinish.conservation_source _ o s hm hz hs hh hl)
 have cr : reference packed o s=ok out := by
  simp only [reference,ct,bind_tc_ok,NKI_ValueFinish.reference,ot,cm,co]
 have cf : JGa_ValueFinish.run packed o s t.range t.selector=ok out := by
  rw [←NKI_ValueFinish.association packed o s t.range t.selector hp ht.2 ht.1]
  simp only [NKI_ValueFinish.reference,cm,co,bind_tc_ok]
 refine ⟨t,_,out,ct,ot,ht,cm,co,hm,ho,cr,?_⟩
 rw [←NKI_ValueFactor.source]
 simp only [NKI_ValueFactor.literal,ct,ot,cf,bind_tc_ok]
#print source
#print axioms source
end AspisR1.NKI_ValueAssociation
end
