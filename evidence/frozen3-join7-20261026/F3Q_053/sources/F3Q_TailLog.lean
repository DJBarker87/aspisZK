import F3Q_TailFacts
import F3Q_TailView
import F3Q_TerminalLog
import F3Q_VerifyAccepted
import F3Q_VerifyCall
import Port4B_SliceReads
import Port4B_Capacity

set_option autoImplicit false
noncomputable section
namespace AspisR1.F3Q_TailLog
open Aeneas Aeneas.Std Result ControlFlow
open MultiproofConeRef
open Port3_NativeBatchCalls (Indices Values)
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open MultiproofConeCanonical MultiproofConeSlices MultiproofConePhysicalViews MultiproofConeSlotTail
attribute [local instance] Classical.propDecidable
attribute [local irreducible] MultiproofConeP6Verify.verifyState MultiproofConeP6Composition.levels

/-- Full accepted native terminal transport. Count, width and padding come
from that SAME accepted iteration; the native verifier supplies its own
source success. Only input provenance and the named P6Boundary remain. -/
theorem accepted {X : Type}
    (D : AspisR1Stage2.aspis_core.digest.Digest32 X) (hash : X) (H : Bytes → State)
    (binary occupied sibling : MultiproofConeP6Callbacks.Parent) (leaf : MultiproofConeP6Batch.Leaf)
    (p6 : MultiproofConeP6Frozen2Stage.P6Boundary (Port4B_VerifyInstall.digest D) hash H binary occupied sibling leaf)
    (proof : Slice U8) (len : proof.val.length=57607)
    (parsed : OraclePortCompactDraft.Parsed) (wire : parsed.wire=bytesOf proof.val)
    (b : Nat) (kind lo n slot : Usize) (hb : b<2) (hk : kind.val<3) (slotValue : slot.val=3*b+kind.val)
    (root : Array U8 32#usize) (rootValue : root=encodeState (OraclePortBatchDraft.committedRoot parsed kind.val))
    (keys : Array U64 16#usize) (s : reference.Scratch) (outIdx : Indices) (outVal : Values)
    (run : Port3_NativeBatchBody.verifier.candidate.batch_tree_loop.body
      (Port3_BatchStd.install (Port4B_VerifyInstall.install Port4B_Install.leaves)) D proof root kind hash lo n slot
      keys s.idx s.val s.n n=ok (.done (outIdx,outVal,some (.Ok ())))) :
    ∃ nodes final,
      Port4B_SlotInstall.nodeSlot proof slot=ok nodes ∧
      bytesOf nodes.val=OraclePortCompactDraft.slice parsed.wire (OraclePortSelectedDraft.slotStart (3*b+kind.val))
        (32*OraclePortSelectedDraft.capacity (3*b+kind.val)) ∧
      (eval H (MultiproofConeP6Batch.tailState (MultiproofConeP6Callbacks.nodeWith occupied sibling)
        parsed b kind.val nodes s)).2=(true,final) ∧ final.idx=outIdx ∧ final.val=outVal ∧
      (eval H (SdkC_Oracle.program (Port9OR_BatchStep.body Port4B_Install.leaves D proof root kind hash
        lo n slot keys s.idx s.val s.n n))).1=
      (eval H (MultiproofConeP6Batch.tailState (MultiproofConeP6Callbacks.nodeWith occupied sibling)
        parsed b kind.val nodes s)).1 := by
  obtain ⟨nodes,supplied,nodeRead,bytes,suppliedEq,well,checks,words,size,verifyRead,terminalLog⟩ :=
    F3Q_TailFacts.accepted D hash H binary occupied sibling leaf p6 proof len parsed wire b kind lo n slot
      hb hk slotValue root rootValue keys s outIdx outVal run
  obtain ⟨final,verified,indices,values⟩ := Port4B_VerifyRun.accepted Port4B_Install.leaves D hash H
    binary occupied sibling leaf p6 root s supplied well words size outIdx outVal verifyRead
  obtain ⟨sourceOut,source,sourceIdx,sourceVal⟩ := F3Q_VerifyCall.returned D hash root s supplied outIdx outVal verifyRead
  have verifierLog := F3Q_VerifyAccepted.log D hash H p6.oracle occupied sibling
    p6.occupied_parent p6.sibling_parent root {s with «at»:=0#usize} sourceOut supplied well words size source
  have combined := terminalLog.trans verifierLog
  rw [suppliedEq,rootValue] at verified combined
  refine ⟨nodes,final,nodeRead,bytes,?_,indices,values,?_⟩
  · simpa only [MultiproofConeP6Batch.tailState,if_pos well,if_pos checks] using verified
  · exact combined.trans (F3Q_TailView.log H (MultiproofConeP6Callbacks.nodeWith occupied sibling) parsed b kind.val nodes s well checks)

#print axioms accepted
end AspisR1.F3Q_TailLog
end
