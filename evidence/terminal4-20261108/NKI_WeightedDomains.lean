import NJB_StubLaws
import NJB_ArrayCarrier
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKI_WeightedDomains
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon decode)
/-- Caller supplement: actual per-cell multiplication clauses imply full raw
weighted-array canonicality/value, without assuming the desired endpoint. -/
theorem source (values weighted : Array NQ 33#usize) (selector : NQ)
 (hv : FIw_ArrayValue.canonical values) (hs : Canon selector)
 (calls : ∀ i,FIq_Native.field.QM31.mul selector (NJB_ArrayCarrier.cell values i)=ok (NJB_ArrayCarrier.cell weighted i)) :
 FIw_ArrayValue.canonical weighted ∧ FIw_ArrayValue.decoded weighted=(fun i=>decode selector*FIw_ArrayValue.decoded values i) := by
 have law : ∀ i,Canon (NJB_ArrayCarrier.cell weighted i) ∧ decode (NJB_ArrayCarrier.cell weighted i)=decode selector*decode (NJB_ArrayCarrier.cell values i) := by
  intro i
  obtain ⟨q,cq,hq,vq⟩ := NJB_StubLaws.qm_mul selector _ hs (NJB_ArrayCarrier.canonical_cell values hv i)
  have eq:=Result.ok.inj (cq.symm.trans (calls i))
  rw [eq] at hq vq
  exact ⟨hq,vq⟩
 refine ⟨?_,funext (fun i=>(law i).2)⟩
 have h:=NJB_ArrayCarrier.canonical_array (NJB_ArrayCarrier.cell weighted) (fun i=>(law i).1)
 simpa only [NJB_ArrayCarrier.array_cell] using h
#print axioms source
end AspisR1.NKI_WeightedDomains
end
