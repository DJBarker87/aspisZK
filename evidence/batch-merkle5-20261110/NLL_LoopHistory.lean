import NLL_LeafStep
import NLL_TerminalHistory
import NLL_TerminalDomain
set_option autoImplicit false
noncomputable section
namespace NLL_LoopHistory
open Aeneas Aeneas.Std Result ControlFlow AspisR1Stage2 AspisR1 MultiproofConeRef NLL
open AspisV8R19.DuplexFrames AspisV8R19.SqueezeOracleBridge

def expected (H : Bytes → AspisV8R19.SourceDuplexStep.State) (p : OraclePortCompactDraft.Parsed)
 (q : Fin 22 → Fin 262144) (batch : Nat) (kind : Usize) (nodes : Slice U8) (root : NLL.Root)
 (positions : List Nat) (s : reference.Scratch) : NLL.History :=
 let leaf:=NKV_LeafBuild.build H p q kind.val positions s
 leaf.1++match leaf.2 with
 | .ok (true,t) => NKV_QueryPlan.tail H batch kind.val nodes root t
 | _ => []

/-- Chronology is proved on the SAME frame fold as the value theorem. Every
leaf, including a rejected duplicate, precedes its comparison; the terminal
verifier history is appended only after the actual count and padding guards. -/
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
 leafHistory kind events=expected H p q batch kind (nodeView H proof slot) root positions f.scratch := by
 induction positions generalizing f events out with
 | nil =>
   have pos : f.position=n := UScalar.eq_of_val_eq (by simpa using span)
   cases native with
   | reject _ more step => exact (lt_irrefl n (pos ▸ more)).elim
   | next _ t more step events out tail => exact (lt_irrefl n (pos ▸ more)).elim
   | terminal _ done events out tail =>
     obtain ⟨read,width,bytes⟩:=NLL_TerminalDomain.source H proof len p wire batch kind slot hb hk slotValue
       (OraclePortFrozenOrder.nodeCount 18 (NJV_UnitDomain.keys f.scratch))
     exact NLL_TerminalHistory.source H root batch kind _ f.scratch width bytes events out tail
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
   | terminal _ done events out tail => exact (done more).elim
   | reject _ more step =>
     rw [indexEq,digestEq] at step
     simp only [leafHistory,event,List.flatMap_cons,List.flatMap_nil,List.append_nil,head,
       expected,NKV_LeafBuild.build,step]
   | next _ t more step events out tail =>
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
       (by change t.n.val+_≤16;simp only [List.length_cons] at room;omega) following events out tail
     change _::leafHistory kind events=_
     rw [head,next]
     simp only [NLL.advance] at *
     unfold expected
     simp only [NKV_LeafBuild.build,refStep,List.cons_append]

set_option pp.proofs false
#print source
#print axioms source
end NLL_LoopHistory
end
