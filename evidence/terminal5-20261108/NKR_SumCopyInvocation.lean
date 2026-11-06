import NKR_SumCopyCollect
import NKR_SumCopyTail
import NJX_PatternRoot
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKR_SumCopyInvocation
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon decode)
open FIq_Native.pool_v1.pair_forest_copy_terminal
open NKR_SumCopyCollect (Lookups)

def zero : Fin 103 → NQ := fun _=>FIq_Native.field.QM31.ZERO

def reference (lookup : Lookups) (s : Selectors) (openings : Array NQ 16#usize)
 (helper lambda chi : NQ) (append : U64) (variant : PoolV1PairForestCompiledVariantV1) :
 Result PoolV1PairForestCompiledCopyTerminalV1 := do
 let patterns ← pattern_values openings lambda
 let scratch ← NJB_StateUpdates.run (fun i state=>NKR_SumCopyCollect.step lookup append variant s i state)
  (List.finRange 136) zero
 let (values,weights) ← NKR_SumFinishInvocation.reference (NJB_ArrayCarrier.array scratch) s patterns
 NKR_SumCopyTail.reference s values weights helper chi

/-- Full218 source invocation support. It is not yet a complete218 row:
the exact optimized tensor/legacy cohort regrouping and native parent-window
certificates remain obligations. All callee Results/domains are nevertheless
internally derived,not supplied as source-success or endpoint premises.
lookup consists only of the reviewed214 native lookup bounds. -/
theorem source (lookup : Lookups) (s : Selectors) (openings : Array NQ 16#usize)
 (helper lambda chi : NQ) (append : U64) (variant : PoolV1PairForestCompiledVariantV1)
 (hh : FIw_ArrayValue.canonical s.high) (hl : FIw_ArrayValue.canonical s.low)
 (ho : FIw_ArrayValue.canonical openings) (hhelper : Canon helper) (hlambda : Canon lambda) (hchi : Canon chi) :
 ∃ (patterns : Array NQ 14#usize) (scratch : Fin 103 → NQ)
   (values weights : Array NQ 4#usize) (active residual scaled : NQ),
 pattern_values openings lambda=ok patterns ∧
 NJB_StateUpdates.run (fun i state=>NKR_SumCopyCollect.step lookup append variant s i state)
  (List.finRange 136) zero=ok scratch ∧
 NKR_SumCopyCollect.Trace lookup append variant s (List.finRange 136) zero scratch ∧
 NKR_SumFinishInvocation.reference (NJB_ArrayCarrier.array scratch) s patterns=ok (values,weights) ∧
 NKR_SumCopyTail.reference s values weights helper chi=ok {residual:=scaled,active:=active} ∧
 reference lookup s openings helper lambda chi append variant=ok {residual:=scaled,active:=active} ∧
 Canon active ∧ Canon residual ∧ Canon scaled ∧
 copy_residual (NKR_SumCopyTail.row values weights) helper chi=ok residual ∧
 decode scaled=decode active*FIw_CopyMeaning.residual (NKR_SumCopyTail.row values weights) (decode helper) (decode chi) := by
 obtain ⟨_,_,patterns,_,_,_,_,_,cp,patternCall⟩ := NJX_PatternRoot.source lambda openings hlambda ho
 obtain ⟨scratch,scratchCall,scratchTrace,cs⟩ := NKR_SumCopyCollect.source lookup append variant s
  (List.finRange 136) zero hh (fun _=>FIv_NativeValue.zero.1)
 obtain ⟨dot,coefficients,finished,_,_,_,_,_,_,_,finishCall,_,_,_,cf,cw,_⟩ :=
  NKR_SumFinishInvocation.source (NJB_ArrayCarrier.array scratch) s patterns
   (NJB_ArrayCarrier.canonical_array _ cs) hh hl cp
 let values : Array NQ 4#usize := NJB_ArrayCarrier.array finished
 let weights : Array NQ 4#usize := NJB_ArrayCarrier.array dot.2
 obtain ⟨active,residual,scaled,acall,ca,rcall,cr,mcall,cm,tailCall,vr,vs⟩ :=
  NKR_SumCopyTail.source s values weights helper chi hh hl
   (NJB_ArrayCarrier.canonical_array _ cf) (NJB_ArrayCarrier.canonical_array _ cw) hhelper hchi
 refine ⟨patterns,scratch,values,weights,active,residual,scaled,patternCall,scratchCall,scratchTrace,
  finishCall,tailCall,?_,ca,cr,cm,rcall,vs⟩
 simp only [reference,patternCall,scratchCall,finishCall,tailCall,bind_tc_ok]

#print source
#print axioms source
end AspisR1.NKR_SumCopyInvocation
end
