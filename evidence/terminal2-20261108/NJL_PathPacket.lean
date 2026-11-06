import NJL_PathFrame
import NJL_OccupancyPacket
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJL_PathPacket
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon decode K)
open NJL_PathContext (Context Domain State)
open NJL_OccupancyPacket (cell)
abbrev Openings := FIq_Native.state_only_poseidon.StateOnlyPoseidonOpenings
theorem size17 : (17#usize).val=17 := by scalar_tac
def pack (s : State) : Array NQ 17#usize := NJB_ArrayCarrier.array (fun i=>s (Fin.cast size17 i))
theorem pack_decode (s : State) (i : Fin (17#usize).val) :
 FIw_ArrayValue.decoded (pack s) i=decode (s (Fin.cast size17 i)) := by
 change decode (NJB_ArrayCarrier.cell (pack s) i)=_
 unfold pack
 exact congrArg decode (congrFun (NJB_ArrayCarrier.cell_array (fun j=>s (Fin.cast size17 j))) i)
def reference (selector : NQ) (o : Openings) : Result (Array NQ 17#usize) := do
 let c ← NJL_PathContext.reference selector (cell o.z 0)
 let out ← NJL_PathTrace.run c (cell o.z) (cell o.succ_z) NJL_PathTrace.jobs (NJL_PathContext.initial c)
 ok (pack out)
/-- All fields are derived by the positive root; no invocation record is an
input. Every actual constructor/field clause and both native side partitions
refer to these SAME caches, opening arrays and source positions. -/
structure Packet (selector : NQ) (o : Openings) where
 context : Context
 residual : NQ
 after : State
 context_call : NJL_PathContext.reference selector (cell o.z 0)=ok context
 context_domain : Domain context
 context_clauses : NJL_PathContext.Clauses selector (cell o.z 0) residual context
 context_cut : ∃ events,NJL_PathContext.Cut selector (cell o.z 0) residual context events context.left context.right (NJL_PathContext.initial context) 6 2
 selected_value : decode context.selected=decode selector*decode (cell o.z 0)
 empty_value : decode context.emptyValue=decode selector*(1-decode (cell o.z 0))
 head_value : decode context.head=decode selector*(decode (cell o.z 0)*(decode (cell o.z 0)-1))
 run_call : NJL_PathTrace.run context (cell o.z) (cell o.succ_z) NJL_PathTrace.jobs (NJL_PathContext.initial context)=ok after
 trace : NJL_PathTrace.Trace context (cell o.z) (cell o.succ_z) NJL_PathTrace.jobs (NJL_PathContext.initial context) after
 canonical : ∀ i,Canon (after i)
 value : ∀ i,decode (after i)=NJL_PathFrame.value context (cell o.z) (cell o.succ_z) i
theorem source (selector : NQ) (o : Openings) (hs : Canon selector)
 (hz : FIw_ArrayValue.canonical o.z) (hb : FIw_ArrayValue.canonical o.succ_z) :
 ∃ p : Packet selector o,reference selector o=ok (pack p.after) ∧ FIw_ArrayValue.canonical (pack p.after) := by
 have hc (i : Fin 16) : Canon (cell o.z i) := hz _ (List.getElem_mem _)
 have hsucc (i : Fin 16) : Canon (cell o.succ_z i) := hb _ (List.getElem_mem _)
 obtain ⟨c,residual,events,cc,cd,clauses,cut,initial,selected,empty,head⟩ := NJL_PathContext.source selector (cell o.z 0) hs (hc _)
 obtain ⟨after,run,trace,ha,va⟩ := NJL_PathFrame.source c (cell o.z) (cell o.succ_z) (NJL_PathContext.initial c) cd hc hsucc initial
 have value (i : Fin 17) : decode (after i)=NJL_PathFrame.value c (cell o.z) (cell o.succ_z) i := by
  rw [va]
  by_cases same : i.val=0
  · have h9 : ¬(9 : Nat) ≤ i.val := by omega
    have h1 : ¬(1 : Nat) ≤ i.val := by omega
    simp only [same,ne_eq,not_true_eq_false,if_false,NJL_PathContext.initial,if_true,NJL_PathFrame.value,if_neg h9,if_neg h1]
    rfl
  · rw [if_pos same]
 let p : Packet selector o :=
  ⟨c,residual,after,cc,cd,clauses,⟨events,cut⟩,selected,empty,head,run,trace,ha,value⟩
 refine ⟨p,?_,?_⟩
 · simp only [reference,cc,run,bind_tc_ok];rfl
 · exact NJB_ArrayCarrier.canonical_array _ (fun _=>ha _)
#print Packet
#print source
#print axioms size17
#print axioms pack_decode
#print axioms source
end AspisR1.NJL_PathPacket
end
