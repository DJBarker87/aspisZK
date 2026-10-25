import Port10AUTH_LoopTail
import Port10AUTH_Tail
import Port9OR_BatchTree

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port10AUTH_Tree
open Aeneas Aeneas.Std Result MultiproofConeRef
open Port3_NativeBatchCalls (Indices Values)
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open MultiproofConeCanonical MultiproofConeSlotState
/-- Accepted native tree transport with complete ordered leaf+verifier reads.
PackedKeys and exact root/wire provenance are VISIBLE input gates, not a
whole-tree agreement or independently successful slot hypothesis. -/
theorem accepted (base : Port3_NativeBatchBody.Ops) {X : Type}
    (D : AspisR1Stage2.aspis_core.digest.Digest32 X) (hash : X) (H : Bytes → State)
    (oracle : CheckpointBytes5Inputs.Oracle D hash H)
    (occupied sibling : MultiproofConeP6Callbacks.Parent) (leaf : MultiproofConeP6Batch.Leaf)
    (occupiedGate : MultiproofConeP6Callbacks.ParentGate (MultiproofConePhysicalTransport.rawOracle H) occupied)
    (siblingGate : MultiproofConeP6Callbacks.ParentGate (MultiproofConePhysicalTransport.rawOracle H) sibling)
    (leafGate : MultiproofConeP6Batch.LeafGate H leaf)
    (proof : Slice U8) (len : proof.val.length=57607)
    (parsed : OraclePortCompactDraft.Parsed) (wire : parsed.wire=bytesOf proof.val)
    (queries : Array U32 22#usize) (q : Fin 22 → Fin 262144) (batch kind : Usize)
    (hb : batch.val<2) (hk : kind.val<3)
    (builder : Port4B_TreeJoin.PackedKeys base queries q batch kind)
    (root : Array U8 32#usize) (rootValue : root=encodeState (OraclePortBatchDraft.committedRoot parsed kind.val))
    (physical : Slice U8) (view : bytesOf physical.val=OraclePortCompactDraft.slice parsed.wire
      (OraclePortSelectedDraft.slotStart (3*batch.val+kind.val)) (32*OraclePortSelectedDraft.capacity (3*batch.val+kind.val)))
    (initial : reference.Scratch) (outIdx : Indices) (outVal : Values)
    (run : Port3_NativeBatchBody.verifier.candidate.batch_tree (Port3_BatchStd.install (Port4B_VerifyInstall.install base))
      D proof queries root batch kind initial.idx initial.val hash=ok (.Ok (),outIdx,outVal)) :
    ∃ final,
      eval H (MultiproofConeP6Batch.batch_tree (MultiproofConeP6Callbacks.nodeWith occupied sibling) leaf
        parsed q batch.val kind.val physical initial)=
        (CheckpointBytes5Inputs.observe (Port9OR_Code.trace D hash
          (Port9OR_BatchTree.code base D hash proof queries root batch kind initial.idx initial.val)).1,(true,final)) ∧
      final.idx=outIdx ∧ final.val=outVal := by
  obtain ⟨raw,sorted,built,sortedCall,loopCall⟩ := Port4B_TreeCuts.keys (Port4B_VerifyInstall.install base)
    D hash proof queries root batch kind initial.idx outIdx initial.val outVal run
  have bounds := Port4B_Bounds.count batch
  have small : (Port4B_TreeCuts.count batch).val≤16 := by rw [bounds.1];split <;> decide
  have positive : 0<(Port4B_TreeCuts.count batch).val := by rw [bounds.1];split <;> decide
  have packed := builder raw built
  obtain ⟨length,stream⟩ := Port4B_SortInstall.key_stream (Port4B_VerifyInstall.install base) q batch.val kind.val
    raw sorted (Port4B_TreeCuts.count batch) small positive packed sortedCall
  have room : (reset initial).n.val+(OraclePortFrozenOrder.sortedPositions q batch.val kind.val).length≤16 := by
    change 0+_≤16;omega
  have small256 : (Port4B_TreeCuts.count batch).val<256 := by omega
  have loopSource := Port9OR_BatchLoop.source base D D hash proof root kind (Port4B_TreeCuts.lo batch)
    (Port4B_TreeCuts.count batch) (Port4B_TreeCuts.slot batch kind) sorted small256
    ((Port4B_TreeCuts.count batch).val+1) initial.idx initial.val 0#usize 0#usize (by simp)
  have loopCode := loopSource.trans loopCall
  obtain ⟨afterLeaf,remaining,fold,terminal,leafLogs⟩ := Port10AUTH_Leaves.accepted base D hash H oracle proof len parsed wire
    q batch.val kind (Port4B_TreeCuts.lo batch) (Port4B_TreeCuts.count batch) (Port4B_TreeCuts.slot batch kind)
    root sorted outIdx outVal (OraclePortFrozenOrder.sortedPositions q batch.val kind.val) (reset initial) 0#usize
    ((Port4B_TreeCuts.count batch).val+1) (fun p hp => hp) bounds.2 (by simpa using length) small room stream loopCode
  obtain ⟨terminalBody,terminalLogs⟩ := Port10AUTH_LoopTail.accepted base D hash proof root kind
    (Port4B_TreeCuts.lo batch) (Port4B_TreeCuts.count batch) (Port4B_TreeCuts.slot batch kind) sorted afterLeaf outIdx outVal
    small256 remaining terminal
  obtain ⟨nodes,final,nodeRead,nodeView,tailValue,indices,values⟩ := Port10AUTH_Tail.accepted base D hash H oracle
    occupied sibling occupiedGate siblingGate proof len parsed wire batch.val kind (Port4B_TreeCuts.lo batch)
    (Port4B_TreeCuts.count batch) (Port4B_TreeCuts.slot batch kind) hb hk (Port4B_Bounds.slot batch kind hb hk)
    root rootValue sorted afterLeaf outIdx outVal terminalBody
  have sameNodes : nodes=physical := Subtype.ext (MultiproofConeByteEquality.bytes_injective (nodeView.trans view.symm))
  subst nodes
  have treeLogs : CheckpointBytes5Inputs.observe (Port9OR_Code.trace D hash
      (Port9OR_BatchTree.code base D hash proof queries root batch kind initial.idx initial.val)).1=
      CheckpointBytes5Inputs.observe (Port9OR_Code.trace D hash
        (Port9OR_BatchLoop.code base D hash proof root kind (Port4B_TreeCuts.lo batch) (Port4B_TreeCuts.count batch)
          (Port4B_TreeCuts.slot batch kind) sorted ((Port4B_TreeCuts.count batch).val+1)
          initial.idx initial.val 0#usize 0#usize)).1 := by
    unfold Port9OR_BatchTree.code
    simp only [Port10AUTH_Leaf.lift_bind,Port9OR_BatchStep.ops,Port3_BatchStd.install,built,sortedCall]
    rw [Port10AUTH_Trace.trace_bind]
    have value := (Port9OR_Code.trace_value D hash _).trans loopCode
    cases h : Port9OR_Code.trace D hash (Port9OR_BatchLoop.code base D hash proof root kind (Port4B_TreeCuts.lo batch)
        (Port4B_TreeCuts.count batch) (Port4B_TreeCuts.slot batch kind) sorted ((Port4B_TreeCuts.count batch).val+1)
        initial.idx initial.val 0#usize 0#usize) with
    | mk log result =>
      rw [h] at value
      dsimp only at value
      rw [value]
      simp only [Port10AUTH_Leaf.pure_trace,List.append_nil]
  change CheckpointBytes5Inputs.observe (Port9OR_Code.trace D hash
    (Port9OR_BatchLoop.code base D hash proof root kind (Port4B_TreeCuts.lo batch) (Port4B_TreeCuts.count batch)
      (Port4B_TreeCuts.slot batch kind) sorted ((Port4B_TreeCuts.count batch).val+1)
      initial.idx initial.val 0#usize 0#usize)).1=_ at leafLogs
  rw [treeLogs,leafLogs,terminalLogs]
  have referenceGate : MultiproofConeP6Batch.LeafGate H MultiproofConeP6Batch.referenceLeaf := by
    intro p q k j s room;rfl
  have sourceFold := MultiproofConeP6Batch.leaves_eq H leaf leafGate parsed q kind.val
    (OraclePortFrozenOrder.sortedPositions q batch.val kind.val) (reset initial) room
  have referenceFold := MultiproofConeP6Batch.leaves_eq H MultiproofConeP6Batch.referenceLeaf referenceGate parsed q kind.val
    (OraclePortFrozenOrder.sortedPositions q batch.val kind.val) (reset initial) room
  have observed := sourceFold.trans (referenceFold.symm.trans fold)
  refine ⟨final,?_,indices,values⟩
  simp only [MultiproofConeP6Batch.batch_tree,eval_bind,observed,eval,List.append_nil,tailValue]


#print axioms accepted
end AspisR1.Port10AUTH_Tree
end
