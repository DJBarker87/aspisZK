import NNC_WeakOps
import NNC_FirstCuts
set_option autoImplicit false
noncomputable section
namespace NNC_WeakReader
open Aeneas Aeneas.Std Result AspisR1 MultiproofConeCanonical S2W_NativeConsolidation
open S2W_ExtractionBoundary

/-- Native reader cut from a parent with only064's slot changed. All selected
reads, range and validator/encoder facts are in the ORIGINAL dictionary. -/
structure Facts (ops auth : AdapterRw.Ops) (id : S2W_ExtractionBoundary.Program)
 (accounts : Accounts) (input : Slice U8) (slot : Slot) (s : SecondCut) : Prop where
 proofIndex : Slice.index_usize accounts 0#usize=ok s.proofAccount
 checkpointIndex : Slice.index_usize accounts 6#usize=ok s.checkpointAccount
 proofRead : AdapterRw.r1_pool_adapter.owned.OwnedAccount.data ops s.proofAccount=ok (.Ok s.raw)
 checkpointRead : AdapterRw.r1_pool_adapter.owned.OwnedAccount.data ops s.checkpointAccount=ok (.Ok s.checkpoint)
 range : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
   s.raw {start:=688#usize,«end»:=s.finish}=ok s.proof
 length : s.raw.val.length=s.finish.val
 suffix : bytesOf s.raw.val=(bytesOf s.raw.val).take 688++bytesOf s.proof.val
 origin : P2P_Origin.Fact ops id accounts input slot s
 native064 : auth.op11 (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 ops)
   s.pub s.proof s.checkpoint () none=ok (.Ok ())

/-- This support inversion consumes a successful weak PARENT, never a
successful064 child hypothesis. Its application to actual entry acceptance
still needs the full parent row's SAME-call native interpretation. -/
theorem from_parent (ops auth : AdapterRw.Ops) (id : S2W_ExtractionBoundary.Program)
 (accounts : Accounts) (input : Slice U8) (slot : Slot)
 (accepted : AdapterRw.r1_pool_adapter.owned.stage2_owned (NNC_WeakOps.replace ops auth)
   id accounts input slot=ok (.Ok ())) :
 ∃ s, Facts ops auth id accounts input slot s := by
 obtain ⟨v,pa,ca,raw,ck,encoded,proof,finish,valid,ip,ic,rp,rc,encode,range,yes,length⟩ :=
   S2X.second_fixed_range (NNC_WeakOps.replace ops auth) id accounts input slot accepted
 rw [NNC_WeakOps.validation] at valid
 rw [NNC_WeakOps.data] at rp rc
 have shape := (AdapterRw.Ranges.suffix_exact raw proof 688#usize finish
   (S2X.successful_range_ordered raw proof 688#usize finish range) length range).2
 change raw.val=raw.val.take 688++proof.val at shape
 have suffix : bytesOf raw.val=(bytesOf raw.val).take 688++bytesOf proof.val := by
   simpa only [bytesOf,List.map_append,List.map_take] using congrArg bytesOf shape
 exact ⟨⟨pa,ca,raw,ck,encoded,proof,finish⟩,
   ⟨ip,ic,rp,rc,range,length,suffix,⟨v,valid,encode⟩,yes⟩⟩

theorem join (ops auth : AdapterRw.Ops) (id : S2W_ExtractionBoundary.Program)
 (e1 e2 : S2W_D189Entry.Entry) (input : Slice U8) (slot : Slot) (saved : alloc.vec.Vec U8)
 (f : FirstCut) (s : SecondCut)
 (first : NNC_FirstCuts.Facts ops e1.first saved f)
 (second : Facts ops auth id (e2.second S2W_D189Wrappers.secondSizes) input slot s) :
 NNC_SourceCuts.Cuts ops e1.first (e2.second S2W_D189Wrappers.secondSizes) saved f s ∧
 P2P_Origin.Fact ops id (e2.second S2W_D189Wrappers.secondSizes) input slot s := by
 exact ⟨⟨first.proofIndex,first.publicIndex,first.proofRead,first.publicRead,first.decode,
   first.first,first.proofLength,first.suffix,second.proofIndex,second.checkpointIndex,
   second.proofRead,second.checkpointRead,second.range,second.length,second.suffix⟩,second.origin⟩

#print axioms from_parent
#print axioms join
end NNC_WeakReader
