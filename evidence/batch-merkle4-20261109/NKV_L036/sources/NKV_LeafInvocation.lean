import NKV_LeafStep
import NKV_ConcreteDomains
import Port4B_KeyDecode
set_option autoImplicit false
noncomputable section
namespace NKV_LeafInvocation
open Aeneas Aeneas.Std Result ControlFlow AspisR1Stage2 AspisR1
open NKV_StepErasure NKV_LoopTransport MultiproofConeRef
open CheckpointBytes5Effect
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge
open MultiproofConeCanonical

/-- Concrete CLOSED opening and private-leaf replies are substituted at SAME
arguments. The one ordered read is before deduplication, even on rejection.
Key/loop invariants are intermediate parent obligations, not root premises. -/
theorem source (H : Bytes → AspisV8R19.SourceDuplexStep.State)
 (proof : Slice U8) (len : proof.val.length=57607)
 (parsed : OraclePortCompactDraft.Parsed) (wire : parsed.wire=bytesOf proof.val)
 (q : Fin 22 → Fin 262144) (batch selected : Nat) (kind lo n slot pos : Usize)
 (root : Array U8 32#usize) (keys : Array U64 16#usize) (s : reference.Scratch)
 (mem : selected∈OraclePortFrozenOrder.sortedPositions q batch kind.val)
 (loValue : lo.val=(if batch=0 then 0 else 10)) (more : pos<n) (room : s.n.val<16)
 (keyRead : Array.index_usize keys pos=ok (MultiproofConeSortOrder.packed q batch kind.val selected))
 (before : Log) :
 ∃ view,(NKV_ConcreteChildren.ops H).op2 proof
     (Port4B_NativeLeaf.openingIndex lo (MultiproofConeSortOrder.packed q batch kind.val selected))=ok view ∧
 view.val.length=832 ∧
 flatten (Port4B_LeafCode.input kind view)=OraclePortSelectedDraft.leaf parsed kind.val selected ∧
 run (NKV_ConcreteChildren.digest H) () (Port4B_LeafCode.code kind view) before=
   ok (encodeState (H (OraclePortSelectedDraft.leaf parsed kind.val selected)),
     before++[(Port4B_LeafCode.input kind view,encodeState (H (OraclePortSelectedDraft.leaf parsed kind.val selected)))]) ∧
 NKV_FRef.verifier.candidate.batch_tree_loop.body (NKV_ConcreteChildren.ops H)
   (NKV_ConcreteChildren.digest H) proof root kind () lo n slot keys s.idx s.val s.n pos=
 (do let out ← reference.leaf_step s (MultiproofConeLeafFold.key q kind.val selected)
       (encodeState (H (OraclePortSelectedDraft.leaf parsed kind.val selected)))
     ok (NKV_LeafStep.project s (Usize.wrapping_add pos 1#usize) out)) := by
 have member := MultiproofConeKeyAdapters.sorted_member q batch kind.val selected mem
 have decoded := Port4B_KeyDecode.packed q batch kind.val selected member lo loValue
 have rebased : (Port4B_NativeLeaf.openingIndex lo (MultiproofConeSortOrder.packed q batch kind.val selected)).val=
   (if batch=0 then 0 else 10)+(MultiproofConeSortOrder.packed q batch kind.val selected).val%256 :=
   decoded.2.trans (MultiproofConeKeyAdapters.packed_opening q batch kind.val selected member).symm
 obtain ⟨view,read,width,contents⟩:=Port4B_Opening.selected proof len parsed wire q batch kind.val selected mem _ rebased
 have actualRead : (NKV_ConcreteChildren.ops H).op2 proof
     (Port4B_NativeLeaf.openingIndex lo (MultiproofConeSortOrder.packed q batch kind.val selected))=ok view := by
   change NJS_Extract.verifier.candidate.opening proof _=ok view
   rw [NKB_CanonicalRows.opening]
   exact read
 have address : flatten (Port4B_LeafCode.input kind view)=OraclePortSelectedDraft.leaf parsed kind.val selected := by
   rw [Port4B_LeafCode.address,contents,MultiproofConeOpeningAdapters.leaf_address]
 have reads:=Port4B_LeafCode.native_and_reads (NKV_ConcreteChildren.digest H) () H
   (by intro parts;rfl) kind view width before
 rw [address] at reads
 have leafRead : (NKV_ConcreteChildren.ops H).op6 (NKV_ConcreteChildren.digest H) () kind view=
     ok (encodeState (H (OraclePortSelectedDraft.leaf parsed kind.val selected))) := by
   rw [NKV_ConcreteDomains.leaf H _ () kind view width]
   exact reads.1
 have indexEq : Port4B_NativeLeaf.decodedIndex (MultiproofConeSortOrder.packed q batch kind.val selected)=
     MultiproofConeLeafFold.key q kind.val selected := UScalar.eq_of_val_eq decoded.1
 have step:=NKV_LeafStep.source (NKV_ConcreteChildren.ops H) (NKV_ConcreteChildren.digest H) ()
   proof root kind lo n slot pos keys s _ view _ more room keyRead actualRead leafRead
 rw [NKV_ConcreteChildren.installed,indexEq] at step
 exact ⟨view,actualRead,width,address,reads.2,step⟩

set_option pp.proofs false
#print source
#print axioms source
end NKV_LeafInvocation
end
