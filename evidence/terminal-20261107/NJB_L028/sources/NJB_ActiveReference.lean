import NJB_ActiveRawHigh
import NJB_ActiveRawLow
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJB_ActiveReference
open Aeneas Aeneas.Std Result FIq_Native.pool_v1.pair_forest_copy_terminal
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon decode K)
def high (s : Selectors) (b : Fin 64) : NQ :=
 s.high.val[b.val]'(by simpa only [s.high.property] using b.isLt)
def low (s : Selectors) (c : Fin 16) : NQ :=
 s.low.val[c.val]'(by simpa only [s.low.property] using c.isLt)
def model (s : Selectors) : R0P.CopySelectors K :=
 { high := fun b=>decode (high s b), low := fun c=>decode (low s c) }
def reference (s : Selectors) : Result NQ := do
 let grouped ← NJB_ActiveRawHigh.run (high s) (List.ofFn (fun b : Fin 64=>b))
  (fun _=>FIq_Native.field.QM31.ZERO)
 NJB_ActiveRawLow.run grouped (low s) (List.ofFn (fun c : Fin 7=>c)) FIq_Native.field.QM31.ZERO
/-- Complete handwritten reference Result, both native step cuts composed by
finite induction. All field replies/domains come from CLOSED emitted laws. -/
theorem result (s : Selectors) (hh : FIw_ArrayValue.canonical s.high)
 (hl : FIw_ArrayValue.canonical s.low) :
 ∃ out,reference s=ok out ∧ Canon out ∧ decode out=R0P.copyActiveLiteral (model s) := by
 have hhigh (b : Fin 64) : Canon (high s b) := hh _ (List.getElem_mem _)
 have hlow (c : Fin 16) : Canon (low s c) := hl _ (List.getElem_mem _)
 obtain ⟨grouped,call,hgrouped,vgrouped⟩ := NJB_ActiveRawHigh.run_result (high s)
  (List.ofFn (fun b : Fin 64=>b)) (fun _=>FIq_Native.field.QM31.ZERO) hhigh
  (fun _=>FIv_NativeValue.zero.1)
 obtain ⟨out,cout,hout,vout⟩ := NJB_ActiveRawLow.run_result grouped (low s)
  (List.ofFn (fun c : Fin 7=>c)) FIq_Native.field.QM31.ZERO hgrouped hlow FIv_NativeValue.zero.1
 refine ⟨out,?_,hout,?_⟩
 · simp only [reference,call,cout,bind_tc_ok]
 · have hz : NJB_ActiveRawHigh.decoded (fun _=>FIq_Native.field.QM31.ZERO)=(fun _=>0) :=
    funext (fun _=>FIv_NativeValue.zero.2)
   rw [hz] at vgrouped
   change decode out=NJB_ActiveModel.lowRun (NJB_ActiveRawHigh.decoded grouped)
    (fun c=>decode (low s c)) (List.ofFn (fun c : Fin 7=>c)) (decode FIq_Native.field.QM31.ZERO) at vout
   rw [vgrouped,FIv_NativeValue.zero.2] at vout
   exact vout.trans (NJB_ActiveModel.result (model s))
/-- Carrier association with the adopted FIq selector decoder, not a second
selector vector or an arbitrary endpoint. -/
theorem model_same (s : Selectors) : model s=FIw_PublicModel.selector s := by
 rfl
#print result
#print axioms result
#print axioms model_same
end AspisR1.NJB_ActiveReference
end
