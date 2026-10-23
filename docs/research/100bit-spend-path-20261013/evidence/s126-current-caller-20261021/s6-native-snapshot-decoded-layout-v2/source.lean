import S6NativeSnapshotPrepareContentsV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace AspisS6NativeSnapshotDecoderFactored.Frames
open AspisR1TerminalDecoder
open pool_v1.pair_tree_profile
open AspisS6NativeSnapshotEncoderGraph
open AspisS6SourceCodec

theorem chunks_contents (bytes : Slice U8) (offset : Nat) (digests : List Digest)
    (frames : chunk_frames bytes offset digests) :
    digests.flatMap DigestContents.chunks=List.slice offset (offset+32*digests.length) bytes.val := by
  induction digests generalizing offset with
  | nil => simp [List.slice]
  | cons digest tail ih =>
    rcases frames with ⟨head,rest⟩
    rw [List.flatMap_cons,head,ih _ rest]
    simpa [Nat.mul_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
      AspisS6SourceCodec.AfterstateFactored.Frames.consecutive_slices bytes.val offset 32 (32*tail.length)

theorem header_prefix (raw : Array U8 800#usize) (frame : header_frame raw) :
    header_bytes=raw.val.take 16 := by
  rcases frame with ⟨magic,h8,h9,h10,h11,h12,h13,h14,h15,format⟩
  have hm : raw.val.take 8=POOL_V1_PAIR_LIVE_SNAPSHOT_MAGIC.val := by
    simpa [List.slice] using magic
  have tail_bytes : List.slice 8 16 raw.val=[raw.val[8]'(by rw [raw.property]; decide),raw.val[9]'(by rw [raw.property]; decide),raw.val[10]'(by rw [raw.property]; decide),raw.val[11]'(by rw [raw.property]; decide),raw.val[12]'(by rw [raw.property]; decide),raw.val[13]'(by rw [raw.property]; decide),raw.val[14]'(by rw [raw.property]; decide),raw.val[15]'(by rw [raw.property]; decide)] := by
    apply List.ext_getElem
    · simp [List.slice,raw.property]
    · intro i hi hj
      have hi8 : i<8 := by simpa using hj
      interval_cases i <;> simp [List.slice]
  have split := AspisS6SliceFrame.take_append_slice raw.val 8 16 (by decide)
  rw [hm,tail_bytes,h8,h9,h10,h11,h12,h13,h14,h15] at split
  simpa [header_bytes,List.replicate_succ,List.append_assoc] using split

theorem decoded_layout (bytes : Slice U8) (snapshot : PoolV1PairLiveSnapshotV1)
    (frame : full_frame bytes snapshot) :
    ∃ format : Array U8 32#usize, POOL_V1_PAIR_TREE_FORMAT_BINDING=ok format ∧
      prefix_bytes snapshot format++snapshot.frontier.val.flatMap DigestContents.chunks=bytes.val := by
  rcases frame with ⟨⟨raw,rawbytes,header⟩,root,frontier,pool,domain,seq,index,validated⟩
  have hheader := header_prefix raw header
  rcases header with ⟨_,_,_,_,_,_,_,_,_,format,fgraph,fbytes⟩
  rw [rawbytes] at hheader fbytes
  refine ⟨format,fgraph,?_⟩
  have hf := chunks_contents bytes 160 snapshot.frontier.val frontier
  have hn : snapshot.frontier.val.length=20 := snapshot.frontier.property
  simp only [hn,Nat.reduceMul,Nat.reduceAdd] at hf
  unfold prefix_bytes
  rw [hheader,fbytes,pool,domain,seq,index,root,hf]
  rw [AspisS6SliceFrame.take_append_slice bytes.val 16 48 (by decide),
    AspisS6SliceFrame.take_append_slice bytes.val 48 80 (by decide),
    AspisS6SliceFrame.take_append_slice bytes.val 80 112 (by decide),
    AspisS6SliceFrame.take_append_slice bytes.val 112 120 (by decide),
    AspisS6SliceFrame.take_append_slice bytes.val 120 128 (by decide),
    AspisS6SliceFrame.take_append_slice bytes.val 128 160 (by decide),
    AspisS6SliceFrame.take_append_slice bytes.val 160 800 (by decide)]
  have hlen : bytes.val.length=800 := rawbytes ▸ raw.property
  simpa only [←hlen,List.take_length]

#print axioms chunks_contents
#print axioms header_prefix
#print axioms decoded_layout
end AspisS6NativeSnapshotDecoderFactored.Frames
