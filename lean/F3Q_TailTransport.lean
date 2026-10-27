import F3Q_TailView
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3Q_TailTransport
open Aeneas Aeneas.Std Result MultiproofConeRef
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open MultiproofConePhysicalViews MultiproofConeSlotTail
attribute [local irreducible] MultiproofConeP6Verify.verifyState

theorem log (H : Bytes → State) (node : MultiproofConeP6Composition.Node)
    (p : OraclePortCompactDraft.Parsed) (b kind : Nat) (nodes supplied : Slice U8) (s : reference.Scratch)
    (root : Array U8 32#usize)
    (rootValue : root=AspisV8R19.SqueezeOracleBridge.encodeState (OraclePortBatchDraft.committedRoot p kind))
    (suppliedEq : supplied=prefixNodes nodes (slotCount s))
    (well : OraclePortFrozenOrder.wellFormed ((live s 0 s.n.val).map Prod.fst))
    (checks : slotCount s≤OraclePortSelectedDraft.capacity (3*b+kind) ∧
      (MultiproofConeCanonical.bytesOf nodes.val).length=32*OraclePortSelectedDraft.capacity (3*b+kind) ∧
      MultiproofConePadding.scan (4*(OraclePortSelectedDraft.capacity (3*b+kind)-slotCount s))
        ((MultiproofConeCanonical.bytesOf nodes.val).drop (32*slotCount s))=true) :
    (eval H (MultiproofConeP6Verify.verifyState node root supplied {s with «at»:=0#usize})).1=
      (eval H (MultiproofConeP6Batch.tailState node p b kind nodes s)).1 := by
  rw [rootValue,suppliedEq]
  exact F3Q_TailView.log H node p b kind nodes s well checks

#print axioms log
end AspisR1.F3Q_TailTransport
end
