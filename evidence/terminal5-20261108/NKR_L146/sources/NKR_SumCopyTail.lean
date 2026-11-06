import NJL_ActiveInvocation
import NJB_CopyResidual
import NKR_SumFinishInvocation
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKR_SumCopyTail
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon decode)
open FIq_Native.pool_v1.pair_forest_copy_terminal

def row (values weights : Array NQ 4#usize) : CopyRowExtension :=
 {producer_values:=Array.make 2#usize [NJB_ArrayCarrier.cell values 0,NJB_ArrayCarrier.cell values 1],
  consumer_values:=Array.make 2#usize [NJB_ArrayCarrier.cell values 2,NJB_ArrayCarrier.cell values 3],
  producer_weights:=Array.make 2#usize [NJB_ArrayCarrier.cell weights 0,NJB_ArrayCarrier.cell weights 1],
  consumer_weights:=Array.make 2#usize [NJB_ArrayCarrier.cell weights 2,NJB_ArrayCarrier.cell weights 3]}

theorem row_canonical (values weights : Array NQ 4#usize)
 (hv : FIw_ArrayValue.canonical values) (hw : FIw_ArrayValue.canonical weights) :
 FIw_ArrayValue.canonical (row values weights).producer_values ∧
 FIw_ArrayValue.canonical (row values weights).producer_weights ∧
 FIw_ArrayValue.canonical (row values weights).consumer_values ∧
 FIw_ArrayValue.canonical (row values weights).consumer_weights := by
 have cv := NJB_ArrayCarrier.canonical_cell values hv
 have cw := NJB_ArrayCarrier.canonical_cell weights hw
 constructor
 · intro q hq
   simp only [row,Array.make,List.mem_cons,List.mem_singleton] at hq
   rcases hq with rfl|rfl <;> exact cv _
 constructor
 · intro q hq
   simp only [row,Array.make,List.mem_cons,List.mem_singleton] at hq
   rcases hq with rfl|rfl <;> exact cw _
 constructor
 · intro q hq
   simp only [row,Array.make,List.mem_cons,List.mem_singleton] at hq
   rcases hq with rfl|rfl <;> exact cv _
 · intro q hq
   simp only [row,Array.make,List.mem_cons,List.mem_singleton] at hq
   rcases hq with rfl|rfl <;> exact cw _

def reference (s : Selectors) (values weights : Array NQ 4#usize) (helper chi : NQ) :
 Result PoolV1PairForestCompiledCopyTerminalV1 := do
 let active ← Selectors.active s
 let residual ← copy_residual (row values weights) helper chi
 let scaled ← FIq_Native.field.QM31.mul active residual
 ok {residual:=scaled,active:=active}

/-- Exact218 tail after220:all8row cells,223active,215residual,and final
field product. Both returned fields and their meanings are retained;every
callee domain is proved from the caller's actual canonical arrays. -/
theorem source (s : Selectors) (values weights : Array NQ 4#usize) (helper chi : NQ)
 (hh : FIw_ArrayValue.canonical s.high) (hl : FIw_ArrayValue.canonical s.low)
 (hv : FIw_ArrayValue.canonical values) (hw : FIw_ArrayValue.canonical weights)
 (hhelper : Canon helper) (hchi : Canon chi) :
 ∃ active residual scaled,
 Selectors.active s=ok active ∧ Canon active ∧
 copy_residual (row values weights) helper chi=ok residual ∧ Canon residual ∧
 FIq_Native.field.QM31.mul active residual=ok scaled ∧ Canon scaled ∧
 reference s values weights helper chi=ok {residual:=scaled,active:=active} ∧
 decode residual=FIw_CopyMeaning.residual (row values weights) (decode helper) (decode chi) ∧
 decode scaled=decode active*FIw_CopyMeaning.residual (row values weights) (decode helper) (decode chi) := by
 obtain ⟨_,active,_,_,ca,_,acall⟩ := NJL_ActiveInvocation.source s hh hl
 obtain ⟨cpv,cpw,ccv,ccw⟩ := row_canonical values weights hv hw
 obtain ⟨residual,rcall,cr,vr⟩ := NJB_CopyResidual.result (row values weights) helper chi cpv ccv cpw ccw hhelper hchi
 obtain ⟨scaled,mcall,cs,vs⟩ := NJB_StubLaws.qm_mul active residual ca cr
 refine ⟨active,residual,scaled,acall,ca,rcall,cr,mcall,cs,?_,vr,?_⟩
 · simp only [reference,acall,rcall,mcall,bind_tc_ok]
 · rw [vs,vr]

#print axioms row_canonical
#print source
#print axioms source
end AspisR1.NKR_SumCopyTail
end
