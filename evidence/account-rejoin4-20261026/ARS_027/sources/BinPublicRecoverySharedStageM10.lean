import SharedFiniteMaterializationM10
import BinPublicRecoveryStageWork
import BinEagerRecoveryWork
import BinRecoveryAddressWork
import BinFrameReplayTotalWork

/-! Complete frame/recovery/public-side staging. Typed words are materialized
into fixed arrays before GS; all list indexing and typed decoding is prepaid.
GS arithmetic and its later cached-array demands are separate. -/
set_option autoImplicit false
namespace AspisR1.BinPublicRecoverySharedStageM10
open BinMerkle32Path
open BinEagerRecoveryWork (materialize materialize_work)
open CanonicalCutEnrichedTranscript (Words)
def typedWords (a b f : List BinEagerWordsReads.Leaf) : Words × Nat :=
  let ca := SharedFiniteMaterializationM10.batch (BinTypedWordDemandWork.c1 a)
  let cb := SharedFiniteMaterializationM10.batch (BinTypedWordDemandWork.c2 b)
  let cf := SharedFiniteMaterializationM10.batch (BinTypedWordDemandWork.finalWord f)
  (⟨ca.1,cb.1,cf.1⟩,ca.2+cb.2+cf.2+16)

attribute [local irreducible] SharedFiniteMaterializationM10.batch

theorem typedWords_value (a b f : List BinEagerWordsReads.Leaf) :
    (typedWords a b f).1 = (BinTypedWordDemandWork.words a b f).1 := by
  rw [BinTypedWordDemandWork.words_value]
  unfold typedWords CanonicalCutEnrichedTranscript.wordsFromMaps
  dsimp only
  congr 1
  · funext i
    exact (SharedFiniteMaterializationM10.value (BinTypedWordDemandWork.c1 a) i).trans
      (BinTypedWordDemandWork.c1_value a i)
  · funext i
    exact (SharedFiniteMaterializationM10.value (BinTypedWordDemandWork.c2 b) i).trans
      (BinTypedWordDemandWork.c2_value b i)
  · funext i
    exact (SharedFiniteMaterializationM10.value (BinTypedWordDemandWork.finalWord f) i).trans
      (BinTypedWordDemandWork.finalWord_value f i)

theorem typedWords_work (a b f : List BinEagerWordsReads.Leaf) :
    (typedWords a b f).2 ≤ 1000000000000 := by
  have ha := SharedFiniteMaterializationM10.work (BinTypedWordDemandWork.c1 a) 311671
    (BinTypedWordDemandWork.c1_work a)
  have hb := SharedFiniteMaterializationM10.work (BinTypedWordDemandWork.c2 b) 295947
    (BinTypedWordDemandWork.c2_work b)
  have hf := SharedFiniteMaterializationM10.work (BinTypedWordDemandWork.finalWord f) 131675
    (BinTypedWordDemandWork.finalWord_work f)
  change _+_+_+16 ≤ _
  omega

def words (log : BinMerkleRecordedLog.Log) (f0 f2 f30 : List Byte) : Words × Nat :=
  let t1 := materialize (fun i : Fin 262144 =>
    BinRecoveryAddressWork.leaf 0x71 480 log f0 false i.val)
  let t2 := materialize (fun i : Fin 262144 =>
    BinRecoveryAddressWork.leaf 0xf1 128 log f2 false i.val)
  let tf := materialize (fun i : Fin 65536 =>
    BinRecoveryAddressWork.leaf 0x72 128 log f30 true i.val)
  let typed := typedWords t1.1 t2.1 tf.1
  (typed.1, t1.2 + t2.2 + tf.2 + typed.2 + 16)

theorem words_work (log : BinMerkleRecordedLog.Log) (f0 f2 f30 : List Byte)
    (h0 : f0.length ≤ 131072) (h2 : f2.length ≤ 131072)
    (h30 : f30.length ≤ 131072) :
    (words log f0 f2 f30).2 ≤ 3000000000000 * (log.length + 1) := by
  have h1 := materialize_work (fun i : Fin 262144 =>
    BinRecoveryAddressWork.leaf 0x71 480 log f0 false i.val)
    (273355 * log.length + 300000) (fun i => BinRecoveryAddressWork.leaf_work _ _ _ _ _ _ (by omega) h0)
  have h2' := materialize_work (fun i : Fin 262144 =>
    BinRecoveryAddressWork.leaf 0xf1 128 log f2 false i.val)
    (273355 * log.length + 300000) (fun i => BinRecoveryAddressWork.leaf_work _ _ _ _ _ _ (by omega) h2)
  have h3 := materialize_work (fun i : Fin 65536 =>
    BinRecoveryAddressWork.leaf 0x72 128 log f30 true i.val)
    (273355 * log.length + 300000) (fun i => BinRecoveryAddressWork.leaf_work _ _ _ _ _ _ (by omega) h30)
  have ht := typedWords_work
    (materialize (fun i : Fin 262144 => BinRecoveryAddressWork.leaf 0x71 480 log f0 false i.val)).1
    (materialize (fun i : Fin 262144 => BinRecoveryAddressWork.leaf 0xf1 128 log f2 false i.val)).1
    (materialize (fun i : Fin 65536 => BinRecoveryAddressWork.leaf 0x72 128 log f30 true i.val)).1
  change _ + _ + _ + _ + 16 ≤ _
  omega

theorem words_value (log : BinMerkleRecordedLog.Log) (f0 f2 f30 : List Byte) :
    (words log f0 f2 f30).1 = (BinEagerRecoveryWork.words log f0 f2 f30).1 := by
  unfold words BinEagerRecoveryWork.words
  rw [typedWords_value, BinTypedWordDemandWork.words_value]
  apply BinEagerWordsReads.maps_congr
  all_goals funext i
  all_goals rw [BinEagerRecoveryWork.materialize_value, BinEagerRecoveryWork.materialize_value,
    BinRecoveryAddressWork.leaf_value]
  all_goals rfl

def stage (run : RawCutProverCompiler.RunView) : Words × Nat :=
  let f0 := BinFrameReplayTotalWork.frameWork run 0
  let f2 := BinFrameReplayTotalWork.frameWork run 2
  let f30 := BinFrameReplayTotalWork.frameWork run 30
  let r := words run.1 f0.1 f2.1 f30.1
  (r.1, f0.2+f2.2+f30.2+r.2)

theorem stage_value (run : RawCutProverCompiler.RunView) :
    (stage run).1 = (BinEagerWordsReads.words run).1 := by
  simp only [stage, words_value, BinFrameReplayTotalWork.frame_value]
  have hv := BinEagerRecoveryWork.stage_value run
  simpa only [BinEagerRecoveryWork.stage, BinFrameReplayReads.frame_value] using hv

theorem stage_work (run : RawCutProverCompiler.RunView) :
    (stage run).2 ≤ 4000000000000*(run.1.length+1) := by
  have hf := BinFrameReplayTotalWork.three_frames_work run
  have hlen (row : Nat) : (BinFrameReplayTotalWork.frameWork run row).1.length ≤ 131072 := by
    rw [BinFrameReplayTotalWork.frame_value, ← BinFrameReplayReads.frame_value]
    exact BinFrameSizeBound.counted_frame_length run row
  have hr := words_work run.1 (BinFrameReplayTotalWork.frameWork run 0).1
    (BinFrameReplayTotalWork.frameWork run 2).1
    (BinFrameReplayTotalWork.frameWork run 30).1 (hlen 0) (hlen 2) (hlen 30)
  change _+_+_+_ ≤ _
  omega

#print axioms typedWords_value
#print axioms typedWords_work
#print axioms words_work
#print axioms words_value
#print axioms stage_value
#print axioms stage_work
end AspisR1.BinPublicRecoverySharedStageM10
