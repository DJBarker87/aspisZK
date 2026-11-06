import NJL_OccupancyFrame
import NJL_OccupancyTail
import NJB_Absorption
import NJB_ArrayCarrier
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJL_OccupancyPacket
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon decode K)
open NJL_OccupancyContext (Context)
open NJL_OccupancyHead (State)
abbrev cell := NJB_Absorption.cell
theorem size12 : (12#usize).val=12 := by scalar_tac
def pack (s : State) : Array NQ 12#usize := NJB_ArrayCarrier.array (fun i=>s (Fin.cast size12 i))
theorem pack_decode (s : State) (i : Fin (12#usize).val) :
 FIw_ArrayValue.decoded (pack s) i=decode (s (Fin.cast size12 i)) := by
 change decode (NJB_ArrayCarrier.cell (pack s) i)=_
 rw [NJB_ArrayCarrier.cell_array]
def reference (input output : NQ) (expected : U32) (opened : Array NQ 16#usize) : Result (Array NQ 12#usize) := do
 let c ← NJL_OccupancyContext.reference input output (cell opened 0)
 let head ← NJL_OccupancyHead.reference c (cell opened 0) (cell opened 1) (cell opened 9)
 let middle ← NJL_OccupancyLanes.run c (cell opened) NJL_OccupancyFrame.indices head
 let last ← NJL_OccupancyTail.reference middle input output (cell opened 0) (cell opened 10) c.oneMinus expected
 ok (pack last)
/-- Derived invocation, never an input hypothesis. Every field is printed and
recorded in NJL_CERTIFICATES; all child clauses and exact native cuts are
conclusions on the SAME source arguments and mutable arrays. -/
structure Packet (input output : NQ) (expected : U32) (opened : Array NQ 16#usize) where
 context : Context
 head : State
 middle : State
 last : State
 context_call : NJL_OccupancyContext.reference input output (cell opened 0)=ok context
 context_domain : NJL_OccupancyContext.Domain context
 context_clauses : NJL_OccupancyContext.Clauses input output (cell opened 0) context
 context_cut : ∃ r events,NJL_OccupancyContext.Cut input output (cell opened 0) r context.empty events 5 1 context
 one_value : decode context.oneMinus=1-decode (cell opened 0)
 both_value : decode context.both=decode input+decode output
 selected_value : decode context.selected=(decode input+decode output)*decode (cell opened 0)
 empty_value : decode context.emptyValue=(decode input+decode output)*(1-decode (cell opened 0))
 head_call : NJL_OccupancyHead.reference context (cell opened 0) (cell opened 1) (cell opened 9)=ok head
 head_cut : ∃ r events,NJL_OccupancyHead.Clauses context (cell opened 0) (cell opened 1) (cell opened 9) r ∧
  NJL_OccupancyHead.Cut context (cell opened 0) (cell opened 1) (cell opened 9) r events context.empty 6 head
 head_value : (fun i=>decode (head i))=NJL_OccupancyHead.model context (cell opened 0) (cell opened 1) (cell opened 9)
 middle_call : NJL_OccupancyLanes.run context (cell opened) NJL_OccupancyFrame.indices head=ok middle
 middle_trace : NJL_OccupancyLanes.Trace context (cell opened) NJL_OccupancyFrame.indices head middle
 middle_value : ∀ i,decode (middle i)=if (3 : Nat) ≤ i.val ∧ i.val < 11 then NJL_OccupancyFrame.value context (cell opened) i else decode (head i)
 last_call : NJL_OccupancyTail.reference middle input output (cell opened 0) (cell opened 10) context.oneMinus expected=ok last
 last_cut : ∃ r events,NJL_OccupancyTail.Clauses input output (cell opened 0) (cell opened 10) context.oneMinus expected r ∧
  NJL_OccupancyTail.Cut middle last input output (cell opened 0) (cell opened 10) context.oneMinus expected r events 5
 last_canonical : ∀ i,Canon (last i)
 last_value : ∀ i,decode (last i)=if i.val=11 then
  decode input*(decode (cell opened 10)*decode context.oneMinus)+decode output*(decode (cell opened 0)-(expected.val : K)) else decode (middle i)
/-- Full positive invocation chain, all caller domains and return frame. -/
theorem source (input output : NQ) (expected : U32) (opened : Array NQ 16#usize)
 (hi : Canon input) (ho : Canon output) (he : expected.val<FIw_ScalarArithmetic.P) (ha : FIw_ArrayValue.canonical opened) :
 ∃ p : Packet input output expected opened,
 reference input output expected opened=ok (pack p.last) ∧ FIw_ArrayValue.canonical (pack p.last) := by
 have hc (i : Fin 16) : Canon (cell opened i) := ha _ (List.getElem_mem _)
 obtain ⟨c,cc,cd,clauses,cut,one,both,selected,empty⟩ := NJL_OccupancyContext.source input output (cell opened 0) hi ho (hc _)
 obtain ⟨rh,head,eh,ch,hclauses,hcut,hh,vh⟩ := NJL_OccupancyHead.source c (cell opened 0) (cell opened 1) (cell opened 9) cd (hc _) (hc _) (hc _)
 obtain ⟨middle,cm,trace,hm,vm⟩ := NJL_OccupancyFrame.source c (cell opened) head cd hc hh
 obtain ⟨rt,last,et,ct,tclauses,tcut,hl,vl⟩ := NJL_OccupancyTail.source middle input output (cell opened 0) (cell opened 10) c.oneMinus expected hm hi ho (hc _) (hc _) cd.1 he
 let p : Packet input output expected opened :=
  ⟨c,head,middle,last,cc,cd,clauses,cut,one,both,selected,empty,ch,⟨rh,eh,hclauses,hcut⟩,vh,
   cm,trace,vm,ct,⟨rt,et,tclauses,tcut⟩,hl,vl⟩
 refine ⟨p,?_,?_⟩
 · simp only [reference,cc,ch,cm,ct,bind_tc_ok];rfl
 · exact NJB_ArrayCarrier.canonical_array _ (fun i=>hl _)
#print Packet
#print source
#print axioms size12
#print axioms pack_decode
#print axioms source
end AspisR1.NJL_OccupancyPacket
end
