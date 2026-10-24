import S6NativeSnapshotEncoderGraphV1
import S6PointWriteFrameV1
import S6NativeSnapshotFrontierContentsV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisS6NativeSnapshotEncoderGraph
open AspisR1TerminalDecoder
open pool_v1.pair_tree_profile
open AspisS6SourceCodec

def header_bytes : List U8 :=
  (POOL_V1_PAIR_LIVE_SNAPSHOT_MAGIC.val++[POOL_V1_PAIR_LIVE_SNAPSHOT_VERSION])++List.replicate 7 0#u8

theorem header_length : header_bytes.length=16 := by
  simp only [header_bytes,List.length_append,List.length_cons,List.length_nil,
    List.length_replicate,POOL_V1_PAIR_LIVE_SNAPSHOT_MAGIC.property]
  decide

theorem header_writes :
    ((List.replicate 800 0#u8).setSlice! 0 POOL_V1_PAIR_LIVE_SNAPSHOT_MAGIC.val).set 8 POOL_V1_PAIR_LIVE_SNAPSHOT_VERSION =
    header_bytes++List.replicate 784 0#u8 := by
  have h0 := AspisS6SliceFrame.setSlice_append_chunk [] POOL_V1_PAIR_LIVE_SNAPSHOT_MAGIC.val 800 0#u8
    (by rw [POOL_V1_PAIR_LIVE_SNAPSHOT_MAGIC.property]; decide)
  simp only [List.length_nil,List.nil_append,POOL_V1_PAIR_LIVE_SNAPSHOT_MAGIC.property,Nat.reduceSub] at h0
  change (List.replicate 800 0#u8).setSlice! 0 POOL_V1_PAIR_LIVE_SNAPSHOT_MAGIC.val =
    POOL_V1_PAIR_LIVE_SNAPSHOT_MAGIC.val++List.replicate 792 0#u8 at h0
  rw [h0]
  have h1 := AspisS6SliceFrame.set_append_point POOL_V1_PAIR_LIVE_SNAPSHOT_MAGIC.val 791 0#u8 POOL_V1_PAIR_LIVE_SNAPSHOT_VERSION
  simp only [POOL_V1_PAIR_LIVE_SNAPSHOT_MAGIC.property,Nat.reduceAdd] at h1
  change (POOL_V1_PAIR_LIVE_SNAPSHOT_MAGIC.val++List.replicate 792 0#u8).set 8 POOL_V1_PAIR_LIVE_SNAPSHOT_VERSION =
    (POOL_V1_PAIR_LIVE_SNAPSHOT_MAGIC.val++[POOL_V1_PAIR_LIVE_SNAPSHOT_VERSION])++List.replicate 791 0#u8 at h1
  rw [h1]
  change _=(POOL_V1_PAIR_LIVE_SNAPSHOT_MAGIC.val++[POOL_V1_PAIR_LIVE_SNAPSHOT_VERSION])++List.replicate 7 0#u8++List.replicate 784 0#u8
  simp only [List.append_assoc,←List.replicate_add]

def prefix_bytes (snapshot : PoolV1PairLiveSnapshotV1) (format : Array U8 32#usize) : List U8 :=
  ((((((header_bytes++format.val)++snapshot.pool.val)++snapshot.deployment_domain.val)++(core.num.U64.to_le_bytes snapshot.sequence).val)++(core.num.U64.to_le_bytes snapshot.next_pair_index).val)++DigestContents.chunks snapshot.current_root)

theorem prefix_length (snapshot : PoolV1PairLiveSnapshotV1) (format : Array U8 32#usize) :
    (prefix_bytes snapshot format).length=160 := by
  simp [prefix_bytes,header_length,format.property,snapshot.pool.property,snapshot.deployment_domain.property,
    (core.num.U64.to_le_bytes snapshot.sequence).property,(core.num.U64.to_le_bytes snapshot.next_pair_index).property,
    PaymentContents.digest_chunks_length]

theorem prepare_contents (snapshot : PoolV1PairLiveSnapshotV1) (format : Array U8 32#usize) :
    (prepare snapshot format).val=prefix_bytes snapshot format++List.replicate 640 0#u8 := by
  unfold prepare
  dsimp only
  rw [header_writes]
  have h0 := AspisS6SliceFrame.setSlice_append_chunk header_bytes (format.val) 784 0#u8 (by simp only [header_length,format.property,snapshot.pool.property,snapshot.deployment_domain.property,(core.num.U64.to_le_bytes snapshot.sequence).property,(core.num.U64.to_le_bytes snapshot.next_pair_index).property,PaymentContents.digest_chunks_length]; decide)
  simp only [List.length_append,header_length,format.property,snapshot.pool.property,snapshot.deployment_domain.property,(core.num.U64.to_le_bytes snapshot.sequence).property,(core.num.U64.to_le_bytes snapshot.next_pair_index).property,PaymentContents.digest_chunks_length,Nat.reduceAdd,Nat.reduceSub] at h0
  change (header_bytes++List.replicate 784 0#u8).setSlice! 16 (format.val) = (header_bytes++format.val)++List.replicate 752 0#u8 at h0
  rw [h0]
  have h1 := AspisS6SliceFrame.setSlice_append_chunk (header_bytes++format.val) (snapshot.pool.val) 752 0#u8 (by simp only [header_length,format.property,snapshot.pool.property,snapshot.deployment_domain.property,(core.num.U64.to_le_bytes snapshot.sequence).property,(core.num.U64.to_le_bytes snapshot.next_pair_index).property,PaymentContents.digest_chunks_length]; decide)
  simp only [List.length_append,header_length,format.property,snapshot.pool.property,snapshot.deployment_domain.property,(core.num.U64.to_le_bytes snapshot.sequence).property,(core.num.U64.to_le_bytes snapshot.next_pair_index).property,PaymentContents.digest_chunks_length,Nat.reduceAdd,Nat.reduceSub] at h1
  change ((header_bytes++format.val)++List.replicate 752 0#u8).setSlice! 48 (snapshot.pool.val) = ((header_bytes++format.val)++snapshot.pool.val)++List.replicate 720 0#u8 at h1
  rw [h1]
  have h2 := AspisS6SliceFrame.setSlice_append_chunk ((header_bytes++format.val)++snapshot.pool.val) (snapshot.deployment_domain.val) 720 0#u8 (by simp only [header_length,format.property,snapshot.pool.property,snapshot.deployment_domain.property,(core.num.U64.to_le_bytes snapshot.sequence).property,(core.num.U64.to_le_bytes snapshot.next_pair_index).property,PaymentContents.digest_chunks_length]; decide)
  simp only [List.length_append,header_length,format.property,snapshot.pool.property,snapshot.deployment_domain.property,(core.num.U64.to_le_bytes snapshot.sequence).property,(core.num.U64.to_le_bytes snapshot.next_pair_index).property,PaymentContents.digest_chunks_length,Nat.reduceAdd,Nat.reduceSub] at h2
  change (((header_bytes++format.val)++snapshot.pool.val)++List.replicate 720 0#u8).setSlice! 80 (snapshot.deployment_domain.val) = (((header_bytes++format.val)++snapshot.pool.val)++snapshot.deployment_domain.val)++List.replicate 688 0#u8 at h2
  rw [h2]
  have h3 := AspisS6SliceFrame.setSlice_append_chunk (((header_bytes++format.val)++snapshot.pool.val)++snapshot.deployment_domain.val) ((core.num.U64.to_le_bytes snapshot.sequence).val) 688 0#u8 (by simp only [header_length,format.property,snapshot.pool.property,snapshot.deployment_domain.property,(core.num.U64.to_le_bytes snapshot.sequence).property,(core.num.U64.to_le_bytes snapshot.next_pair_index).property,PaymentContents.digest_chunks_length]; decide)
  simp only [List.length_append,header_length,format.property,snapshot.pool.property,snapshot.deployment_domain.property,(core.num.U64.to_le_bytes snapshot.sequence).property,(core.num.U64.to_le_bytes snapshot.next_pair_index).property,PaymentContents.digest_chunks_length,Nat.reduceAdd,Nat.reduceSub] at h3
  change ((((header_bytes++format.val)++snapshot.pool.val)++snapshot.deployment_domain.val)++List.replicate 688 0#u8).setSlice! 112 ((core.num.U64.to_le_bytes snapshot.sequence).val) = ((((header_bytes++format.val)++snapshot.pool.val)++snapshot.deployment_domain.val)++(core.num.U64.to_le_bytes snapshot.sequence).val)++List.replicate 680 0#u8 at h3
  rw [h3]
  have h4 := AspisS6SliceFrame.setSlice_append_chunk ((((header_bytes++format.val)++snapshot.pool.val)++snapshot.deployment_domain.val)++(core.num.U64.to_le_bytes snapshot.sequence).val) ((core.num.U64.to_le_bytes snapshot.next_pair_index).val) 680 0#u8 (by simp only [header_length,format.property,snapshot.pool.property,snapshot.deployment_domain.property,(core.num.U64.to_le_bytes snapshot.sequence).property,(core.num.U64.to_le_bytes snapshot.next_pair_index).property,PaymentContents.digest_chunks_length]; decide)
  simp only [List.length_append,header_length,format.property,snapshot.pool.property,snapshot.deployment_domain.property,(core.num.U64.to_le_bytes snapshot.sequence).property,(core.num.U64.to_le_bytes snapshot.next_pair_index).property,PaymentContents.digest_chunks_length,Nat.reduceAdd,Nat.reduceSub] at h4
  change (((((header_bytes++format.val)++snapshot.pool.val)++snapshot.deployment_domain.val)++(core.num.U64.to_le_bytes snapshot.sequence).val)++List.replicate 680 0#u8).setSlice! 120 ((core.num.U64.to_le_bytes snapshot.next_pair_index).val) = (((((header_bytes++format.val)++snapshot.pool.val)++snapshot.deployment_domain.val)++(core.num.U64.to_le_bytes snapshot.sequence).val)++(core.num.U64.to_le_bytes snapshot.next_pair_index).val)++List.replicate 672 0#u8 at h4
  rw [h4]
  have h5 := AspisS6SliceFrame.setSlice_append_chunk (((((header_bytes++format.val)++snapshot.pool.val)++snapshot.deployment_domain.val)++(core.num.U64.to_le_bytes snapshot.sequence).val)++(core.num.U64.to_le_bytes snapshot.next_pair_index).val) (DigestContents.chunks snapshot.current_root) 672 0#u8 (by simp only [header_length,format.property,snapshot.pool.property,snapshot.deployment_domain.property,(core.num.U64.to_le_bytes snapshot.sequence).property,(core.num.U64.to_le_bytes snapshot.next_pair_index).property,PaymentContents.digest_chunks_length]; decide)
  simp only [List.length_append,header_length,format.property,snapshot.pool.property,snapshot.deployment_domain.property,(core.num.U64.to_le_bytes snapshot.sequence).property,(core.num.U64.to_le_bytes snapshot.next_pair_index).property,PaymentContents.digest_chunks_length,Nat.reduceAdd,Nat.reduceSub] at h5
  change ((((((header_bytes++format.val)++snapshot.pool.val)++snapshot.deployment_domain.val)++(core.num.U64.to_le_bytes snapshot.sequence).val)++(core.num.U64.to_le_bytes snapshot.next_pair_index).val)++List.replicate 672 0#u8).setSlice! 128 (DigestContents.chunks snapshot.current_root) = ((((((header_bytes++format.val)++snapshot.pool.val)++snapshot.deployment_domain.val)++(core.num.U64.to_le_bytes snapshot.sequence).val)++(core.num.U64.to_le_bytes snapshot.next_pair_index).val)++DigestContents.chunks snapshot.current_root)++List.replicate 640 0#u8 at h5
  rw [h5]
  rfl

#print axioms header_writes
#print axioms prefix_length
#print axioms prepare_contents
end AspisS6NativeSnapshotEncoderGraph
