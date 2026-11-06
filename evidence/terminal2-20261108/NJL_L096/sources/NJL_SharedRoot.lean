import NJL_SharedTrace
import NJL_SharedMeaning
import NJB_DecodeInjective
import NHU_Preweighted
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJL_SharedRoot
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon decode)
open NJB_ArrayCarrier (cell array)
def reference (packed : Array NQ 24#usize) (values : Array NQ 33#usize) (selector : NQ) : Result (Array NQ 24#usize) := do
 let after ← NJB_SharedReference.reference (cell values) selector (cell packed)
 ok (array (N:=24#usize) after)
/-- Complete deployed N33/start49 native/reference/adopted packet. Each
cohort weighted input is the actual selector*value Result on SAME arguments;
all24 final cells agree with the adopted add_preweighted, including both
zero-padded boundary groups. No stronger generic start/N claim is made. -/
theorem source (packed : Array NQ 24#usize) (values : Array NQ 33#usize) (selector : NQ)
 (hp : FIw_ArrayValue.canonical packed) (hv : FIw_ArrayValue.canonical values) (hc : Canon selector) :
 ∃ (weighted : Array NQ 33#usize) (after : NJL_SharedCuts.State),
 (∀ i,FIq_Native.field.QM31.mul selector (cell values i)=ok (cell weighted i)) ∧
 reference packed values selector=ok (array (N:=24#usize) after) ∧
 NJL_SharedTrace.Trace (cell values) selector (List.finRange 9) (cell packed) after ∧
 FIq_Native.pool_v1.pair_forest_semantic_terminal.add_preweighted packed 49#usize weighted=ok (array (N:=24#usize) after) ∧
 FIw_ArrayValue.canonical (array (N:=24#usize) after) ∧
 (∀ j,FIw_ArrayValue.decoded (array (N:=24#usize) after) j=FIw_ArrayValue.decoded packed j+
 FIx_SelectedMeaning.contribution (fun i=>decode selector*FIw_ArrayValue.decoded values i) 49 j.val) := by
 have cv := NJB_ArrayCarrier.canonical_cell values hv
 have cp := NJB_ArrayCarrier.canonical_cell packed hp
 obtain ⟨after,call,trace,ha⟩ := NJL_SharedTrace.source (cell values) selector (List.finRange 9) (cell packed) cv hc cp
 obtain ⟨other,otherCall,_,otherValue⟩ := NJB_SharedReference.result (cell values) selector (cell packed) cv hc cp
 have same : after=other := Result.ok.inj (call.symm.trans otherCall)
 have decoded : ∀ j,decode (after j)=decode (cell packed j)+FIx_SelectedMeaning.contribution
   (fun i=>decode selector*decode (cell values i)) 49 j.val := by
  intro j
  rw [same]
  exact (congrFun otherValue j).trans (NJL_SharedMeaning.value _ _ _ j)
 choose weights laws using (fun i=>NJB_StubLaws.qm_mul selector (cell values i) hc (cv i))
 let weighted : Array NQ 33#usize := array (N:=33#usize) weights
 have cw : FIw_ArrayValue.canonical weighted := NJB_ArrayCarrier.canonical_array _ (fun i=>(laws i).2.1)
 obtain ⟨adopted,adoptedCall,adoptedCanon,adoptedValue⟩ := NHU_Preweighted.result packed 49#usize weighted (by decide) (by decide) hp cw
 have exactCarrier : adopted=array (N:=24#usize) after := by
  apply Subtype.ext
  apply List.ext_getElem
  · simp only [adopted.property,Array.make,List.length_ofFn,array]
  · intro i hi hj
    let j : Fin (24#usize).val := ⟨i,by simpa only [adopted.property] using hi⟩
    have eq : cell adopted j=after j := by
     apply NJB_DecodeInjective.qm _ _ (NJB_ArrayCarrier.canonical_cell adopted adoptedCanon j) (ha j)
     have value := adoptedValue j
     have weightedValue : FIw_ArrayValue.decoded weighted=(fun k=>decode selector*decode (cell values k)) := by
      funext k
      change decode (cell (array (N:=33#usize) weights) k)=_
      rw [NJB_ArrayCarrier.cell_array]
      exact (laws k).2.2
     rw [weightedValue] at value
     exact value.trans (decoded j).symm
    simpa only [cell,array,Array.make,List.getElem_ofFn,j] using eq
 refine ⟨weighted,after,?_,?_,trace,?_,NJB_ArrayCarrier.canonical_array _ ha,?_⟩
 · intro i
   change FIq_Native.field.QM31.mul selector (cell values i)=ok (cell (array (N:=33#usize) weights) i)
   rw [NJB_ArrayCarrier.cell_array]
   exact (laws i).1
 · simp only [reference,NJB_SharedReference.reference,call,bind_tc_ok]
 · simpa only [exactCarrier] using adoptedCall
 · intro j
   change decode (cell (array (N:=24#usize) after) j)=_
   rw [NJB_ArrayCarrier.cell_array]
   exact decoded j
#print source
#print axioms source
end AspisR1.NJL_SharedRoot
end
