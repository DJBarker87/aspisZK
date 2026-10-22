import MultiproofConePhysicalVerify
import MultiproofConeCountPhysicalLevels
import MultiproofConePadding

set_option autoImplicit false
noncomputable section
namespace AspisR1.MultiproofConeSlotTail
open Aeneas Aeneas.Std Result MultiproofConeRef
open MultiproofConePhysicalProgram MultiproofConePhysicalViews MultiproofConePhysicalTransport
open OraclePortFrozenOrder OraclePortSelectedDraft OraclePortCompactDraft
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
attribute [local instance] Classical.propDecidable

def prefixNodes (nodes : Slice U8) (count : Nat) : Slice U8 :=
  ⟨nodes.val.take (32*count),by
    have bound := nodes.property
    simp only [List.length_take];omega⟩

theorem prefix_bytes (nodes : Slice U8) (count : Nat) :
    remaining (prefixNodes nodes count) 0#usize =
      (MultiproofConeCanonical.bytesOf nodes.val).take (32*count) := by
  simp only [remaining,prefixNodes,show (0#usize).val=0 from rfl,List.drop_zero,
    MultiproofConeCanonical.bytesOf,List.map_take]

/-- Exact live index view of the physical scratch, including arbitrary suffix. -/
theorem keys_view (s : reference.Scratch) :
    MultiproofConeCountPhysical.cells (MultiproofConeLivePreservation.keys s) 0 s.n.val=
      (live s 0 s.n.val).map Prod.fst := by
  simp only [MultiproofConeCountPhysical.cells,MultiproofConeLivePreservation.keys,
    live,MultiproofConePhysicalLive.view,List.map_map,Function.comp_def,
    decodeEntry,MultiproofConePhysicalLive.cell,Nat.zero_add]

def slotCount (s : reference.Scratch) : Nat :=
  MultiproofConeCountPhysicalLevels.physicalCount 18 (MultiproofConeLivePreservation.keys s) s.n.val

theorem slot_count_eq (s : reference.Scratch) :
    slotCount s=nodeCount 18 ((live s 0 s.n.val).map Prod.fst) := by
  rw [slotCount,MultiproofConeCountPhysicalLevels.physical_count_eq,keys_view]

/-- The post-leaf source-shaped tail: index-only count, whole-word padding,
physical eighteen-level execution, then physical root/consumption comparison.
The caller supplies the exact fixed slot view; no byte-equality conclusion is
assumed about the oracle program. -/
def tail (p : Parsed) (batch kind : Nat) (nodes : Slice U8) (s : reference.Scratch) :
    Program Bytes State Bool :=
  let is := (live s 0 s.n.val).map Prod.fst
  if wellFormed is then
    let count := slotCount s
    let cap := capacity (3*batch+kind)
    let bs := MultiproofConeCanonical.bytesOf nodes.val
    if count≤cap ∧ bs.length=32*cap ∧
        MultiproofConePadding.scan (4*(cap-count)) (bs.drop (32*count))=true then
      MultiproofConePhysicalVerify.verify (encodeState (OraclePortBatchDraft.committedRoot p kind))
        (prefixNodes nodes count) {s with «at»:=0#usize}
    else .done false
  else .done false

/-- Accepted count/padding/root composition. The only carrier equation is the
exact physical fixed-slot view, independently checked by the caller adapter. -/
theorem accepted_tail {X : Type} (D : aspis_core.digest.Digest32 X) (hash : X)
    (H : Bytes → State) (law : ∀ input, D.digest hash input=ok (rawOracle H input))
    (p : Parsed) (batch kind : Nat) (nodes : Slice U8) (s : reference.Scratch)
    (slot : MultiproofConeCanonical.bytesOf nodes.val=
      slice p.wire (slotStart (3*batch+kind)) (32*capacity (3*batch+kind)))
    (accepted : (eval H (tail p batch kind nodes s)).2=true) :
    eval H (tail p batch kind nodes s)=eval H (slotTail p batch kind (live s 0 s.n.val)) := by
  let is := (live s 0 s.n.val).map Prod.fst
  by_cases wf : wellFormed is
  · have count : slotCount s=nodeCount 18 is := slot_count_eq s
    let cap := capacity (3*batch+kind)
    let bs := MultiproofConeCanonical.bytesOf nodes.val
    by_cases checks : slotCount s≤cap ∧ bs.length=32*cap ∧
        MultiproofConePadding.scan (4*(cap-slotCount s))
          (bs.drop (32*slotCount s))=true
    · have source : tail p batch kind nodes s=
          MultiproofConePhysicalVerify.verify (encodeState (OraclePortBatchDraft.committedRoot p kind))
            (prefixNodes nodes (nodeCount 18 is)) {s with «at»:=0#usize} := by
        simp only [tail,show wellFormed ((live s 0 s.n.val).map Prod.fst) from wf,if_true]
        change (if _ then _ else _)=_
        rw [if_pos checks,count]
      have counted : nodeCount 18 is≤cap ∧ bs.length=32*cap := by rw [←count];exact ⟨checks.1,checks.2.1⟩
      have padding : bs.drop (32*nodeCount 18 is)=List.replicate (32*(cap-nodeCount 18 is)) 0 := by
        apply (MultiproofConePadding.padding cap (nodeCount 18 is) bs counted.2 counted.1).mp
        simpa only [count] using checks.2.2
      have verified := MultiproofConePhysicalVerify.accepted_verify D hash H law
        (encodeState (OraclePortBatchDraft.committedRoot p kind)) (prefixNodes nodes (nodeCount 18 is))
        {s with «at»:=0#usize} (by rfl) (by simpa only [source] using accepted)
      have modelChecks : nodeCount 18 is≤cap ∧
          (slice p.wire (slotStart (3*batch+kind)) (32*cap)).length=32*cap ∧
          (slice p.wire (slotStart (3*batch+kind)) (32*cap)).drop (32*nodeCount 18 is)=
            List.replicate (32*(cap-nodeCount 18 is)) 0 := by
        rw [←slot];exact ⟨counted.1,counted.2,padding⟩
      have modelUnfold : slotTail p batch kind (live s 0 s.n.val)=
          verifyInPlace (OraclePortBatchDraft.committedRoot p kind) (live s 0 s.n.val)
            (bs.take (32*nodeCount 18 is)) := by
        unfold slotTail
        rw [if_pos wf]
        change (if _ then _ else _)=_
        rw [if_pos modelChecks]
        rw [←slot]
      change eval H (MultiproofConePhysicalVerify.verify
        (encodeState (OraclePortBatchDraft.committedRoot p kind))
        (prefixNodes nodes (nodeCount 18 is)) {s with «at»:=0#usize}) =
        eval H (verifyInPlace (decodeState (encodeState (OraclePortBatchDraft.committedRoot p kind)))
          (live s 0 s.n.val) (remaining (prefixNodes nodes (nodeCount 18 is)) 0#usize)) at verified
      rw [state_roundtrip,prefix_bytes] at verified
      rw [source,modelUnfold]
      exact verified
    · have reject : tail p batch kind nodes s=.done false := by
        unfold tail
        rw [if_pos wf]
        exact if_neg checks
      rw [reject] at accepted
      cases accepted
  · simp only [tail,show ¬wellFormed ((live s 0 s.n.val).map Prod.fst) from wf,if_false,eval] at accepted
    cases accepted

#print axioms prefix_bytes
#print axioms keys_view
#print axioms slot_count_eq
#print axioms accepted_tail
end AspisR1.MultiproofConeSlotTail
end
