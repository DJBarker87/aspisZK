import NKV_ConcreteDomains
import Port4B_SortInstall
set_option autoImplicit false
noncomputable section
namespace NKV_KeyInvocation
open Aeneas Aeneas.Std Result AspisR1
open AspisV8R19.DuplexFrames
abbrev HashState := AspisV8R19.SourceDuplexStep.State

/-- Actual CLOSED key producer then actual CLOSED sort, at SAME arguments.
Its returned array itself supplies every later indexed key; there is no
independently chosen stream, arbitrary operation slot, or child-success premise. -/
theorem source (H : Bytes → HashState) (raw : Array U32 22#usize) (batch : Nat) (kind : Usize)
 (hb : batch<2) (hk : kind.val<3) (canonical : ∀ j,j<22 → raw.val[j]!.val<262144) :
 ∃ sorted,
 (do let keys ← (NKV_ConcreteChildren.ops H).op4 raw (NKB_KeyStream.lo batch) (NKB_KeyStream.count batch) kind
     (NKV_ConcreteChildren.ops H).op5 keys (NKB_KeyStream.count batch))=ok sorted ∧
 (OraclePortFrozenOrder.sortedPositions (Port4B_KeyInstall.queries raw) batch kind.val).length=
   (NKB_KeyStream.count batch).val ∧
 Port4B_LeafLoop.KeyStream (Port4B_KeyInstall.queries raw) batch kind.val sorted 0#usize
   (OraclePortFrozenOrder.sortedPositions (Port4B_KeyInstall.queries raw) batch kind.val) := by
 have positive:=NKB_KeyStream.positive batch
 have initial:=NKB_KeyStream.initial raw batch kind
 obtain ⟨out,run,front,frame⟩:=MultiproofConeSortOrder.sorted_positions (Port4B_KeyInstall.queries raw)
   batch kind.val (Port4B_KeyInstall.keyArray raw batch kind.val) (NKB_KeyStream.count batch)
   (by omega) initial
 have one : MultiproofSortRef.sort_reference.sort_rows (Port4B_KeyInstall.keyArray raw batch kind.val)
     1#usize (NKB_KeyStream.count batch)=ok out := by
   rw [←MultiproofConeSortOrder.source_start_one _ _ positive.1]
   exact run
 have stream:=Port4B_SortInstall.key_stream (NKV_ConcreteChildren.ops H) (Port4B_KeyInstall.queries raw)
   batch kind.val (Port4B_KeyInstall.keyArray raw batch kind.val) out (NKB_KeyStream.count batch)
   (by omega) positive.1 initial one
 refine ⟨out,?_,stream⟩
 change (do let keys ← NJS_Extract.verifier.candidate.batch_keys raw _ _ kind
            NJS_Extract.verifier.candidate.sort_batch_keys keys _)=ok out
 rw [NKB_KeyStream.built raw batch kind hk hb canonical]
 simp only [bind_tc_ok]
 rw [NJS_Sort.source _ _ positive.1 (by omega)]
 exact one

#print source
#print axioms source
end NKV_KeyInvocation
end
