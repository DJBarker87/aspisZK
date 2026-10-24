from pathlib import Path
import sys
R=Path(__file__).resolve().parents[2];L=R/'docs/research/100bit-spend-path-20261013/lean'
s=(L/'Port4B_TreeJoin.lean').read_text();s=s[s.index('/-- Accepted native tree'):]
s=s[:s.index('#print axioms accepted')]
a=s.index('    (binary occupied sibling');b=s.index('    (proof : Slice U8)',a)
s=s[:a]+'''    (oracle : CheckpointBytes5Inputs.Oracle D hash H)
    (occupied sibling : MultiproofConeP6Callbacks.Parent) (leaf : MultiproofConeP6Batch.Leaf)
    (occupiedGate : MultiproofConeP6Callbacks.ParentGate (MultiproofConePhysicalTransport.rawOracle H) occupied)
    (siblingGate : MultiproofConeP6Callbacks.ParentGate (MultiproofConePhysicalTransport.rawOracle H) sibling)
    (leafGate : MultiproofConeP6Batch.LeafGate H leaf)
'''+s[b:]
s=s.replace('PackedKeys base','Port4B_TreeJoin.PackedKeys base')
a=s.index('    ∃ afterLeaf final,');b=s.index(' := by',a)
s=s[:a]+'''    ∃ final,
      eval H (MultiproofConeP6Batch.batch_tree (MultiproofConeP6Callbacks.nodeWith occupied sibling) leaf
        parsed q batch.val kind.val physical initial)=
        (CheckpointBytes5Inputs.observe (Port9OR_Code.trace D hash
          (Port9OR_BatchTree.code base D hash proof queries root batch kind initial.idx initial.val)).1,(true,final)) ∧
      final.idx=outIdx ∧ final.val=outVal'''+s[b:]
a=s.index('  obtain ⟨afterLeaf,fold,terminal⟩');b=s.index('  have referenceGate',a)
s=s[:a]+'''  have small256 : (Port4B_TreeCuts.count batch).val<256 := by omega
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
'''+s[b:]
s=s.replace('p6.leaf','leafGate').replace('  refine ⟨afterLeaf,final,?_,indices,values⟩','  refine ⟨final,?_,indices,values⟩')
header='''import Port10AUTH_LoopTail
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
'''
out=header+s+'\n#print axioms accepted\nend AspisR1.Port10AUTH_Tree\nend\n';p=L/'Port10AUTH_Tree.lean'
if '--check' in sys.argv:assert p.read_text()==out
else:p.write_text(out)
