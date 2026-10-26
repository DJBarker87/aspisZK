import MultiproofConeP6Batch
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3Q_TailView
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open MultiproofConePhysicalViews MultiproofConeSlotTail
attribute [local irreducible] MultiproofConeP6Verify.verifyState

theorem log (H : Bytes → State) (node : MultiproofConeP6Composition.Node)
    (p : OraclePortCompactDraft.Parsed) (b kind : Nat) (nodes : Slice U8) (s : reference.Scratch)
    (well : OraclePortFrozenOrder.wellFormed ((live s 0 s.n.val).map Prod.fst))
    (checks : slotCount s≤OraclePortSelectedDraft.capacity (3*b+kind) ∧
      (MultiproofConeCanonical.bytesOf nodes.val).length=32*OraclePortSelectedDraft.capacity (3*b+kind) ∧
      MultiproofConePadding.scan (4*(OraclePortSelectedDraft.capacity (3*b+kind)-slotCount s))
        ((MultiproofConeCanonical.bytesOf nodes.val).drop (32*slotCount s))=true) :
    (eval H (MultiproofConeP6Verify.verifyState node
      (AspisV8R19.SqueezeOracleBridge.encodeState (OraclePortBatchDraft.committedRoot p kind))
      (prefixNodes nodes (slotCount s)) {s with «at»:=0#usize})).1=
      (eval H (MultiproofConeP6Batch.tailState node p b kind nodes s)).1 := by
  rw [MultiproofConeP6Batch.tailState,if_pos well,if_pos checks]

#print axioms log
end AspisR1.F3Q_TailView
end
