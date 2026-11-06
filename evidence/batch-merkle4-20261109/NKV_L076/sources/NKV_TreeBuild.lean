import NKV_TreeEntry
import NKV_LeafTraversal
set_option autoImplicit false
noncomputable section
namespace NKV_TreeBuild
open Aeneas Aeneas.Std Result AspisR1Stage2 AspisR1 MultiproofConeRef
open NKV_StepErasure NKV_ReturnBoundary
open AspisV8R19.DuplexFrames
abbrev HashState := AspisV8R19.SourceDuplexStep.State

/-- Whole direct reference, through the real key producer/sort and every leaf
outcome. The only remainder is its concrete post-leaf tail, reached solely by
the complete source build. No arbitrary Ops, stream or child-success premise. -/
theorem source (H : Bytes → HashState) (proof : Slice U8) (len : proof.val.length=57607)
 (parsed : OraclePortCompactDraft.Parsed) (wire : parsed.wire=MultiproofConeCanonical.bytesOf proof.val)
 (raw : Array U32 22#usize) (root : Array U8 32#usize) (batch kind : Usize)
 (hb : batch.val<2) (hk : kind.val<3) (canonical : ∀ j,j<22 → raw.val[j]!.val<262144)
 (idx : Indices) (val : Values) :
 ∃ keys,NKV_FRef.verifier.candidate.batch_tree (NKV_ConcreteChildren.ops H) (NKV_ConcreteChildren.digest H)
   proof raw root batch kind idx val ()=
 (NKV_LeafTraversal.finish H proof root kind (NKB_KeyStream.lo batch.val) (NKB_KeyStream.count batch.val)
   (Usize.wrapping_add (Usize.wrapping_mul 3#usize batch) kind) keys
   (NKV_LeafBuild.build H parsed (Port4B_KeyInstall.queries raw) kind.val
     (OraclePortFrozenOrder.sortedPositions (Port4B_KeyInstall.queries raw) batch.val kind.val)
     (NJV_EntryABI.initial idx val 0#usize)).2 >>= returned) := by
 obtain ⟨keys,length,stream,entry⟩:=NKV_TreeEntry.source H proof raw root batch kind hb hk canonical idx val
 have positive:=NKB_KeyStream.positive batch.val
 have low : (NKB_KeyStream.lo batch.val).val=(if batch.val=0 then 0 else 10) := by
   unfold NKB_KeyStream.lo
   split <;> scalar_tac
 have room : (NJV_EntryABI.initial idx val 0#usize).n.val+
     (OraclePortFrozenOrder.sortedPositions (Port4B_KeyInstall.queries raw) batch.val kind.val).length≤16 := by
   rw [length]
   change 0+_≤16
   omega
 have traversal:=NKV_LeafTraversal.source H proof len parsed wire (Port4B_KeyInstall.queries raw)
   batch.val kind (NKB_KeyStream.lo batch.val) (NKB_KeyStream.count batch.val)
   (Usize.wrapping_add (Usize.wrapping_mul 3#usize batch) kind) root keys _
   (NJV_EntryABI.initial idx val 0#usize) 0#usize (fun _ mem=>mem) low
   (by change 0+_= _;omega) (by omega) room stream
 exact ⟨keys,entry.trans (congrArg (fun out => out >>= returned) traversal)⟩

set_option pp.proofs false
#print source
#print axioms source
end NKV_TreeBuild
end
