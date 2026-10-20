import BinCutRecoveryWork
import BinFrameSizeBound
import BinEagerWordsReads

/-! The entire eager recovery batch, including all failed parses and walks,
with bounded byte comparisons, prefix copies and table/list allocation events.
Frame generation/replay, public parsing and GS are outside this stage. Cached
indexing during later word demands belongs to the consuming continuation. -/
set_option autoImplicit false
namespace AspisR1.BinEagerRecoveryWork
open BinMerkle32Path
open CanonicalCutEnrichedTranscript (Words wordsFromMaps)
abbrev Leaf := BinEagerWordsReads.Leaf
abbrev RunView := RawCutProverCompiler.RunView

def materialize {n : Nat} (f : Fin n → Leaf × Nat) : List Leaf × Nat :=
  let t := BinEagerWordsReads.materialize f
  (t.1, t.2 + 3 * n + 1)

theorem materialize_value {n : Nat} (f : Fin n → Leaf × Nat) (i : Fin n) :
    BinEagerWordsReads.cached (materialize f).1 i = (f i).1 :=
  BinEagerWordsReads.materialize_value f i

theorem materialize_work {n : Nat} (f : Fin n → Leaf × Nat) (c : Nat)
    (h : ∀ i, (f i).2 ≤ c) : (materialize f).2 ≤ n * (c + 3) + 1 := by
  have ht := BinEagerWordsReads.materialize_reads f c h
  change _ + 3 * n + 1 ≤ _
  nlinarith

def leaf (tag : Byte) (width : Nat) (log : BinMerkleRecordedLog.Log)
    (frame : List Byte) (root : Digest) (i : Nat) : Leaf × Nat :=
  let r := BinCutRecoveryWork.recover tag width frame log (BinMultiproof.slots 18 i) root
  (r.1.map Prod.fst, r.2 + 4)

theorem leaf_value (tag : Byte) (width : Nat) (log : BinMerkleRecordedLog.Log)
    (frame : List Byte) (root : Digest) (i : Nat) :
    (leaf tag width log frame root i).1 =
      (BinEagerWordsReads.leafRead tag width log frame root i).1 := by
  simp only [leaf, BinCutRecoveryWork.recover_value, BinEagerWordsReads.leafRead,
    BinRecordedRecoveryReads.cutRecover_value]

theorem leaf_work (tag : Byte) (width : Nat) (log : BinMerkleRecordedLog.Log)
    (frame : List Byte) (root : Digest) (i : Nat)
    (hw : width ≤ 480) (hf : frame.length ≤ 131072) :
    (leaf tag width log frame root i).2 ≤ 273355 * log.length + 115 := by
  have h := BinCutRecoveryWork.recover_work tag width frame log
    (BinMultiproof.slots 18 i) root hw (by rw [BinMultiproof.slots_length])
  have hm := Nat.mul_le_mul_right log.length
    (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hf) 11211)
  change _ + 4 ≤ _
  omega

def words (log : BinMerkleRecordedLog.Log) (f0 f2 f30 : List Byte) : Words × Nat :=
  let t1 := materialize (fun i : Fin 262144 =>
    leaf 0x71 480 log f0 (RawCutWordsFromView.rootFrom 8 f0) i.val)
  let t2 := materialize (fun i : Fin 262144 =>
    leaf 0xf1 128 log f2 (RawCutWordsFromView.rootFrom 8 f2) i.val)
  let tf := materialize (fun i : Fin 65536 =>
    leaf 0x72 128 log f30 (RawCutWordsFromView.rootFrom 9 f30) i.val)
  (wordsFromMaps (BinEagerWordsReads.cached t1.1)
    (BinEagerWordsReads.cached t2.1) (BinEagerWordsReads.cached tf.1),
    t1.2 + t2.2 + tf.2 + 16)

theorem words_work (log : BinMerkleRecordedLog.Log) (f0 f2 f30 : List Byte)
    (h0 : f0.length ≤ 131072) (h2 : f2.length ≤ 131072)
    (h30 : f30.length ≤ 131072) :
    (words log f0 f2 f30).2 ≤ 1000000000000 * (log.length + 1) := by
  have h1 := materialize_work (fun i : Fin 262144 =>
    leaf 0x71 480 log f0 (RawCutWordsFromView.rootFrom 8 f0) i.val)
    (273355 * log.length + 115) (fun i => leaf_work _ _ _ _ _ _ (by omega) h0)
  have h2' := materialize_work (fun i : Fin 262144 =>
    leaf 0xf1 128 log f2 (RawCutWordsFromView.rootFrom 8 f2) i.val)
    (273355 * log.length + 115) (fun i => leaf_work _ _ _ _ _ _ (by omega) h2)
  have h3 := materialize_work (fun i : Fin 65536 =>
    leaf 0x72 128 log f30 (RawCutWordsFromView.rootFrom 9 f30) i.val)
    (273355 * log.length + 115) (fun i => leaf_work _ _ _ _ _ _ (by omega) h30)
  change _ + _ + _ + 16 ≤ _
  omega

def stage (run : RunView) : Words × Nat :=
  words run.1 (BinFrameReplayReads.frameCount run 0).1
    (BinFrameReplayReads.frameCount run 2).1 (BinFrameReplayReads.frameCount run 30).1

attribute [local irreducible] BinFrameReplayReads.frameCount

theorem stage_value (run : RunView) : (stage run).1 = (BinEagerWordsReads.words run).1 := by
  unfold stage words BinEagerWordsReads.words
  apply BinEagerWordsReads.maps_congr
  all_goals funext i
  all_goals rw [materialize_value, BinEagerWordsReads.materialize_value, leaf_value]

theorem stage_work (run : RunView) :
    (stage run).2 ≤ 1000000000000 * (run.1.length + 1) :=
  words_work _ _ _ _ (BinFrameSizeBound.counted_frame_length run 0)
    (BinFrameSizeBound.counted_frame_length run 2)
    (BinFrameSizeBound.counted_frame_length run 30)

theorem stage_bounded_log (run : RunView) (Q : Nat) (hlog : run.1.length ≤ Q + 1161) :
    (stage run).2 ≤ 1000000000000 * (Q + 1162) :=
  (stage_work run).trans (Nat.mul_le_mul_left _ (Nat.add_le_add_right hlog 1))

#print axioms materialize_value
#print axioms materialize_work
#print axioms leaf_value
#print axioms leaf_work
#print axioms words_work
#print axioms stage_value
#print axioms stage_work
#print axioms stage_bounded_log
end AspisR1.BinEagerRecoveryWork
