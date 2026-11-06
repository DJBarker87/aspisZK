import NLL_LeafStep
import NLL_TerminalStep
import NLL_TerminalDomain
set_option autoImplicit false
noncomputable section
namespace NLL_LoopValue
open Aeneas Aeneas.Std Result ControlFlow AspisR1Stage2 AspisR1 MultiproofConeRef NLL
open AspisV8R19.DuplexFrames AspisV8R19.SqueezeOracleBridge

/-- Full native cut fold. The stream is an intermediate entry invariant; the
root constructs it using the actual CLOSED key/sort calls. The terminal byte
gate is derived internally from the SAME original proof and slot. -/
theorem source (H : Bytes → AspisV8R19.SourceDuplexStep.State)
 (proof : Slice U8) (len : proof.val.length=57607)
 (p : OraclePortCompactDraft.Parsed) (wire : p.wire=MultiproofConeCanonical.bytesOf proof.val)
 (q : Fin 22 → Fin 262144) (batch : Nat) (kind lo n slot : Usize) (root : NLL.Root)
 (hb : batch<2) (hk : kind.val<3) (slotValue : slot.val=3*batch+kind.val)
 (loValue : lo.val=(if batch=0 then 0 else 10)) (small : n.val≤16)
 (positions : List Nat) (f : Frame)
 (members : ∀ selected∈positions,selected∈OraclePortFrozenOrder.sortedPositions q batch kind.val)
 (span : f.position.val+positions.length=n.val) (room : f.scratch.n.val+positions.length≤16)
 (stream : Port4B_LeafLoop.KeyStream q batch kind.val f.keys f.position positions)
 (events : List Event) (out : NLL.Answer)
 (native : Loop H proof root batch kind lo n slot f events out) :
 (NKV_FRef.verifier.candidate.batch_tree_loop (NKV_ConcreteChildren.ops H)
   (NKV_ConcreteChildren.digest H) proof root kind f.scratch.idx f.scratch.val () lo n slot f.keys
     f.scratch.n f.position >>= NKV_ReturnBoundary.returned)=ok out := by
 induction positions generalizing f events out with
 | nil =>
   have pos : f.position=n := UScalar.eq_of_val_eq (by simpa using span)
   cases native with
   | reject _ more step => exact (lt_irrefl n (pos ▸ more)).elim
   | next _ t more step events out tail => exact (lt_irrefl n (pos ▸ more)).elim
   | terminal _ done events out tail =>
     obtain ⟨read,width,bytes⟩:=NLL_TerminalDomain.source H proof len p wire batch kind slot hb hk slotValue
       (OraclePortFrozenOrder.nodeCount 18 (NJV_UnitDomain.keys f.scratch))
     rw [pos]
     exact NLL_TerminalStep.value H proof len p wire root batch kind lo n slot hb hk slotValue f.keys
       f.scratch (by simpa using room) _ read bytes events out tail
 | cons selected rest ih =>
   have more : f.position<n := by change f.position.val<n.val;simp only [List.length_cons] at span;omega
   have bound : f.scratch.n.val<16 := by simp only [List.length_cons] at room;omega
   have keyRead : Array.index_usize f.keys f.position=ok (MultiproofConeSortOrder.packed q batch kind.val selected) :=
     stream f.position 0 (by simp) (by omega)
   obtain ⟨indexEq,address,digestEq,body⟩:=NLL_LeafStep.source H proof len p wire q batch selected kind lo n slot root f
     (members selected (by simp)) loValue more bound keyRead
   cases native with
   | terminal _ done events out tail => exact (done more).elim
   | reject _ more step =>
     unfold NKV_FRef.verifier.candidate.batch_tree_loop
     rw [Aeneas.Std.loop.eq_def]
     simp only [Aeneas.Std.uncurry,body,step,bind_tc_ok,NKV_LeafStep.project,NKV_ReturnBoundary.returned]
   | next _ t more step events out tail =>
     have exactStep := step
     rw [indexEq,digestEq,MultiproofConeLeafContent.step_exact f.scratch _ _ bound] at exactStep
     have count:=MultiproofConeLeafFold.next_bound f.scratch _ _ bound t (Result.ok.inj exactStep)
     have inc:=Port3_Wrapping.increment f.position (by omega)
     have following : Port4B_LeafLoop.KeyStream q batch kind.val (advance f t).keys (advance f t).position rest := by
       intro cursor j hj value
       change cursor.val=(Usize.wrapping_add f.position 1#usize).val+j at value
       have read:=stream cursor (j+1) (by simpa only [List.length_cons] using Nat.succ_lt_succ hj)
         (by rw [inc] at value;omega)
       simpa only [List.getElem_cons_succ,advance] using read
     have next:=ih (advance f t) (fun pos hp => members pos (List.mem_cons_of_mem _ hp))
       (by change (Usize.wrapping_add f.position 1#usize).val+_= _;rw [inc];simp only [List.length_cons] at span;omega)
       (by change t.n.val+_≤16;simp only [List.length_cons] at room;omega) following events out tail
     conv_lhs => unfold NKV_FRef.verifier.candidate.batch_tree_loop
     rw [Aeneas.Std.loop.eq_def]
     simp only [Aeneas.Std.uncurry,body,step,bind_tc_ok,NKV_LeafStep.project]
     exact next

set_option pp.proofs false
#print source
#print axioms source
end NLL_LoopValue
end
