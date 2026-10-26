import Port4B_TreeJoin
import Port4B_Bounds
import F3Q_TreeCode
import F3Q_LeafLoop
import F3Q_TailLog

set_option autoImplicit false
noncomputable section
namespace AspisR1.F3Q_TreeLog
open Aeneas Aeneas.Std Result
open MultiproofConeRef
open Port3_NativeBatchCalls (Indices Values)
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open MultiproofConeCanonical MultiproofConeSlotState

abbrev PackedKeys := Port4B_TreeJoin.PackedKeys

/-- Accepted native tree transport with complete ordered leaf+verifier reads.
PackedKeys and exact root/wire provenance are VISIBLE input gates, not a
whole-tree agreement or independently successful slot hypothesis. -/
theorem accepted {X : Type}
    (D : AspisR1Stage2.aspis_core.digest.Digest32 X) (hash : X) (H : Bytes → State)
    (binary occupied sibling : MultiproofConeP6Callbacks.Parent) (leaf : MultiproofConeP6Batch.Leaf)
    (p6 : MultiproofConeP6Frozen2Stage.P6Boundary (Port4B_VerifyInstall.digest D) hash H binary occupied sibling leaf)
    (proof : Slice U8) (len : proof.val.length=57607)
    (parsed : OraclePortCompactDraft.Parsed) (wire : parsed.wire=bytesOf proof.val)
    (queries : Array U32 22#usize) (q : Fin 22 → Fin 262144) (batch kind : Usize)
    (hb : batch.val<2) (hk : kind.val<3)
    (builder : PackedKeys Port4B_Install.leaves queries q batch kind)
    (root : Array U8 32#usize) (rootValue : root=encodeState (OraclePortBatchDraft.committedRoot parsed kind.val))
    (physical : Slice U8) (view : bytesOf physical.val=OraclePortCompactDraft.slice parsed.wire
      (OraclePortSelectedDraft.slotStart (3*batch.val+kind.val)) (32*OraclePortSelectedDraft.capacity (3*batch.val+kind.val)))
    (initial : reference.Scratch) (outIdx : Indices) (outVal : Values)
    (run : Port3_NativeBatchBody.verifier.candidate.batch_tree (Port3_BatchStd.install (Port4B_VerifyInstall.install Port4B_Install.leaves))
      D proof queries root batch kind initial.idx initial.val hash=ok (.Ok (),outIdx,outVal)) :
    ∃ afterLeaf final,
      eval H (MultiproofConeP6Batch.batch_tree (MultiproofConeP6Callbacks.nodeWith occupied sibling) leaf
        parsed q batch.val kind.val physical initial)=
        ((OraclePortFrozenOrder.sortedPositions q batch.val kind.val).map
          (fun p => (OraclePortSelectedDraft.leaf parsed kind.val p,H (OraclePortSelectedDraft.leaf parsed kind.val p))) ++
          (eval H (MultiproofConeP6Batch.tailState (MultiproofConeP6Callbacks.nodeWith occupied sibling)
            parsed batch.val kind.val physical afterLeaf)).1,(true,final)) ∧
      final.idx=outIdx ∧ final.val=outVal ∧
      (eval H (SdkC_Oracle.program (Port9OR_BatchTree.code Port4B_Install.leaves D hash proof queries root batch kind initial.idx initial.val))).1=
      (eval H (MultiproofConeP6Batch.batch_tree (MultiproofConeP6Callbacks.nodeWith occupied sibling) leaf
        parsed q batch.val kind.val physical initial)).1 := by
  obtain ⟨raw,sorted,built,sortedCall,loopCall⟩ := Port4B_TreeCuts.keys (Port4B_VerifyInstall.install Port4B_Install.leaves)
    D hash proof queries root batch kind initial.idx outIdx initial.val outVal run
  have bounds := Port4B_Bounds.count batch
  have small : (Port4B_TreeCuts.count batch).val≤16 := by rw [bounds.1];split <;> decide
  have positive : 0<(Port4B_TreeCuts.count batch).val := by rw [bounds.1];split <;> decide
  have packed := builder raw built
  obtain ⟨length,stream⟩ := Port4B_SortInstall.key_stream (Port4B_VerifyInstall.install Port4B_Install.leaves) q batch.val kind.val
    raw sorted (Port4B_TreeCuts.count batch) small positive packed sortedCall
  have room : (reset initial).n.val+(OraclePortFrozenOrder.sortedPositions q batch.val kind.val).length≤16 := by
    change 0+_≤16;omega
  obtain ⟨afterLeaf,fold,terminal,leafLogs⟩ := F3Q_LeafLoop.accepted
    D hash H p6.oracle proof len parsed wire q batch.val kind (Port4B_TreeCuts.lo batch)
    (Port4B_TreeCuts.count batch) (Port4B_TreeCuts.slot batch kind) root sorted outIdx outVal
    (OraclePortFrozenOrder.sortedPositions q batch.val kind.val) (reset initial) 0#usize
    (fun p hp => hp) bounds.2 (by simpa using length) small room stream loopCall
  have terminalBody := Port4B_TreeCuts.terminal (Port4B_VerifyInstall.install Port4B_Install.leaves) D hash proof root kind
    (Port4B_TreeCuts.lo batch) (Port4B_TreeCuts.count batch) (Port4B_TreeCuts.slot batch kind) afterLeaf.n
    sorted afterLeaf.idx outIdx afterLeaf.val outVal terminal
  obtain ⟨nodes,final,nodeRead,nodeView,tailValue,indices,values,tailLogs⟩ := F3Q_TailLog.accepted D hash H
    binary occupied sibling leaf p6 proof len parsed wire batch.val kind (Port4B_TreeCuts.lo batch)
    (Port4B_TreeCuts.count batch) (Port4B_TreeCuts.slot batch kind) hb hk (Port4B_Bounds.slot batch kind hb hk)
    root rootValue sorted afterLeaf outIdx outVal terminalBody
  have sameNodes : nodes=physical := Subtype.ext (MultiproofConeByteEquality.bytes_injective (nodeView.trans view.symm))
  subst nodes
  have referenceGate : MultiproofConeP6Batch.LeafGate H MultiproofConeP6Batch.referenceLeaf := by
    intro p q k j s room;rfl
  have sourceFold := MultiproofConeP6Batch.leaves_eq H leaf p6.leaf parsed q kind.val
    (OraclePortFrozenOrder.sortedPositions q batch.val kind.val) (reset initial) room
  have referenceFold := MultiproofConeP6Batch.leaves_eq H MultiproofConeP6Batch.referenceLeaf referenceGate parsed q kind.val
    (OraclePortFrozenOrder.sortedPositions q batch.val kind.val) (reset initial) room
  have observed := sourceFold.trans (referenceFold.symm.trans fold)
  refine ⟨afterLeaf,final,?_,indices,values,?_⟩
  · simp only [MultiproofConeP6Batch.batch_tree,eval_bind,observed,eval,List.append_nil,tailValue]
  · have sourceCode := F3Q_TreeCode.log D hash H p6.oracle proof root queries batch kind initial.idx outIdx initial.val outVal
      raw sorted built sortedCall (by omega) loopCall
    have sameFuel : (OraclePortFrozenOrder.sortedPositions q batch.val kind.val).length+1=
        (Port4B_TreeCuts.count batch).val+1 := by omega
    rw [←sameFuel] at sourceCode
    have together := sourceCode.trans (leafLogs.trans (congrArg
      (List.append ((OraclePortFrozenOrder.sortedPositions q batch.val kind.val).map
        (fun pos=>(OraclePortSelectedDraft.leaf parsed kind.val pos,H (OraclePortSelectedDraft.leaf parsed kind.val pos))))) tailLogs))
    simpa only [MultiproofConeP6Batch.batch_tree,eval_bind,observed] using together

#print axioms accepted
end AspisR1.F3Q_TreeLog
end
