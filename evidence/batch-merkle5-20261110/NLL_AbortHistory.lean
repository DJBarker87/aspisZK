import NLL_Prefix
import NLL_TerminalDomain
set_option autoImplicit false
noncomputable section
namespace NLL_AbortHistory
open Aeneas Aeneas.Std Result ControlFlow AspisR1Stage2 AspisR1 MultiproofConeRef NLL
open AspisV8R19.DuplexFrames AspisV8R19.SqueezeOracleBridge
attribute [local instance] Classical.propDecidable

/-- Each runtime abort retains exactly the answered prefix and the SAME next
physical request. No return, pending digest reply, or later call is assumed. -/
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
 (events : List Event) (pending : Pending)
 (native : AbortLoop H proof root batch kind lo n slot f events pending) :
 NLL_Prefix.At (NLL_LoopHistory.expected H p q batch kind (nodeView H proof slot) root positions f.scratch)
   (leafHistory kind events++pending.answered) pending.parts := by
 induction positions generalizing f events pending with
 | nil =>
   have pos : f.position=n := UScalar.eq_of_val_eq (by simpa using span)
   cases native with
   | leaf _ more => exact (lt_irrefl n (pos ▸ more)).elim
   | next _ t more step events pending tail => exact (lt_irrefl n (pos ▸ more)).elim
   | verify _ done well fits pad queries request state child =>
     obtain ⟨read,width,bytes⟩:=NLL_TerminalDomain.source H proof len p wire batch kind slot hb hk slotValue
       (OraclePortFrozenOrder.nodeCount 18 (NJV_UnitDomain.keys f.scratch))
     have packet:=(NJV_TX2.abort H root _ f.scratch.idx f.scratch.val f.scratch.n bytes queries request state child).1
     have lengths : (NJV_AdoptedObservation.history queries).length=queries.length := by
       simp only [NJV_AdoptedObservation.history,List.length_map]
     change NLL_Prefix.At (NKV_QueryPlan.tail H batch kind.val (nodeView H proof slot) root f.scratch)
       (NJV_AdoptedObservation.history queries) (NJP_RequestTransport.address request)
     unfold NKV_QueryPlan.tail NLL_Prefix.At
     rw [if_pos well,if_pos ⟨fits,pad⟩,lengths]
     exact packet
 | cons selected rest ih =>
   have more : f.position<n := by change f.position.val<n.val;simp only [List.length_cons] at span;omega
   have bound : f.scratch.n.val<16 := by simp only [List.length_cons] at room;omega
   have keyRead : Array.index_usize f.keys f.position=ok (MultiproofConeSortOrder.packed q batch kind.val selected) :=
     stream f.position 0 (by simp) (by omega)
   obtain ⟨indexEq,address,digestEq,body⟩:=NLL_LeafStep.source H proof len p wire q batch selected kind lo n slot root f
     (members selected (by simp)) loValue more bound keyRead
   have head : (flatten (Port4B_LeafCode.input kind (view H proof lo (key f))),decodeState (digest H proof kind lo f))=
       (OraclePortSelectedDraft.leaf p kind.val selected,H (OraclePortSelectedDraft.leaf p kind.val selected)) := by
     rw [address,digestEq,state_roundtrip]
   cases native with
   | verify _ done well fits pad queries request state child => exact (done more).elim
   | leaf _ more =>
     exact NLL_Prefix.first H p q batch kind _ root selected rest f.scratch _ address
   | next _ t more step events pending tail =>
     have refStep:=step
     rw [indexEq,digestEq] at refStep
     have exactStep:=refStep
     rw [MultiproofConeLeafContent.step_exact f.scratch _ _ bound] at exactStep
     have count:=MultiproofConeLeafFold.next_bound f.scratch _ _ bound t (Result.ok.inj exactStep)
     have inc:=Port3_Wrapping.increment f.position (by omega)
     have following : Port4B_LeafLoop.KeyStream q batch kind.val (NLL.advance f t).keys (NLL.advance f t).position rest := by
       intro cursor j hj value
       change cursor.val=(Usize.wrapping_add f.position 1#usize).val+j at value
       have read:=stream cursor (j+1) (by simpa only [List.length_cons] using Nat.succ_lt_succ hj)
         (by rw [inc] at value;omega)
       simpa only [List.getElem_cons_succ,NLL.advance] using read
     have next:=ih (NLL.advance f t) (fun pos hp => members pos (List.mem_cons_of_mem _ hp))
       (by change (Usize.wrapping_add f.position 1#usize).val+_= _;rw [inc];simp only [List.length_cons] at span;omega)
       (by change t.n.val+_≤16;simp only [List.length_cons] at room;omega) following events pending tail
     rw [NLL_Prefix.next H p q batch kind _ root selected rest f.scratch t refStep]
     change NLL_Prefix.At (_::_) ((_::leafHistory kind events)++pending.answered) pending.parts
     rw [head]
     exact NLL_Prefix.cons _ _ _ _ next

set_option pp.proofs false
#print source
#print axioms source
end NLL_AbortHistory
end
