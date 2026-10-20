import BinCompiledRunWordStability
import LiteralTableWordChoiceBin
import RWireRawCutLiteralAllFrames
import RWireConstructedWords
import RWireRawByteLaterTableWords
import RWireRawByteCutTable

/-! The commitment-derived words are also the words recoverable from the
single later first-read table.  The later frame is explicit so the proof does
not assume a table snapshot at an earlier commitment cut. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.RWireRawCutLaterTableLiteralWords

open FS FS2 FS2.Duplex
open AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisR1.RawCutWordsFromView
open AspisR1.RWireConstructedWords
open AspisR1.RawCutProverCompiler
open AspisR1.RWireRawByteLaterTableWords
open AspisR1.RWireRawByteTableWords
open AspisR1.CanonicalCutEnrichedTranscript (Words wordsFromMaps)
open BinCanonicalCutWords
open AspisR1.BinRawByteCollisionTargets
open BinMerkle32Path BinMerkle32Leaf BinMerkleTable BinMerkleLeafRecovery BinMerkleRecordedLog

private def tableC1Map (tr : List (Bytes × State)) (current : Bytes) (root : State) :
    Fin 262144 → Option (List CanonicalCutEnrichedTranscript.Byte) := fun leaf =>
  (recoverFromTable (tableBefore emptyTable tr current) 0x71 480
    (BinMultiproof.slots 18 leaf.val) root).map Prod.fst

private def tableC2Map (tr : List (Bytes × State)) (current : Bytes) (root : State) :
    Fin 262144 → Option (List CanonicalCutEnrichedTranscript.Byte) := fun leaf =>
  (recoverFromTable (tableBefore emptyTable tr current) 0xf1 128
    (BinMultiproof.slots 18 leaf.val) root).map Prod.fst

private def tableFoldedMap (tr : List (Bytes × State)) (current : Bytes) (root : State) :
    Fin 65536 → Option (List CanonicalCutEnrichedTranscript.Byte) := fun leaf =>
  (recoverFromTable (tableBefore emptyTable tr current) 0x72 128
    (BinMultiproof.slots 18 leaf.val) root).map Prod.fst

/-- A commitment map can be recovered from the current first-read table when
its commitment is earlier, or when the current frame is that same commitment. -/
theorem recover_current_table_eq_full
    (iv : State) (H : Bytes → State) (tr : List (Bytes × State)) (Q : Nat)
    (hcons : ∀ q ∈ tr, q.2 = H q.1)
    (hQ : firstReads emptyTable tr ≤ Q)
    (hout : ¬ hitsBad (AllAddressCollision.bad iv BinRawByteCollisionTargets.pred Q) emptyTable tr)
    (current commitment : Bytes) (root : State) (tag : BinMerkle32Path.Byte) (width : Nat)
    (j : Fin 5) (hcurrent : Read tr current) (hcommit : Read tr commitment)
    (hpred : BinRawByteCollisionTargets.pred j commitment = some root)
    (horder : Before tr commitment current ∨ commitment = current) :
    (fun slots => recoverFromTable (tableBefore emptyTable tr current) tag width slots root) =
      (fun slots => BinRawByteCutStability.recoverAt tag width tr slots root) := by
  rcases horder with hbefore | heq
  · exact RWireRawByteLaterTableWords.recover_later_table_eq_full iv H tr Q hcons hQ hout
      tag width root commitment current j hbefore hpred
  · subst current
    exact RWireRawByteTableWords.recover_table_eq_full iv H tr Q commitment hcons hQ hout
      tag width root j hcurrent hpred

private theorem before_n_steps
    (tr : List (Bytes × State)) (frame : Nat → Bytes) (N : Nat)
    (hadj : ∀ i, i < N → Before tr (frame i) (frame (i + 1))) :
    ∀ n, ∀ i, 0 < n → i + n ≤ N → Before tr (frame i) (frame (i + n)) := by
  intro n
  induction n with
  | zero => intro i hn; omega
  | succ n ih =>
      intro i hn hbound
      have hfirst := hadj i (by omega)
      cases n with
      | zero => simpa using hfirst
      | succ n =>
          have htail := ih (i + 1) (by omega) (by omega)
          have hindex : i + 1 + (n + 1) = i + (n + 2) := by omega
          rw [hindex] at htail
          exact before_trans tr hfirst htail

private theorem actual_frame_order_or_eq
    (decoder : LiteralByteProtocol.Decoder)
    (d : RawCutTranscriptRun.ErasedPrefix → RawCutTranscriptRun.ErasedMessage → Bool)
    (prover : Prover) (H : Bytes → State) (run : RawCutProverCompiler.RunView)
    (hrun : run = eval H (experiment prover (verifier decoder d)))
    (iv : State) (Q : Nat)
    (hQ : firstReads emptyTable run.1 ≤ Q)
    (hout : ¬ hitsBad (AllAddressCollision.bad iv BinRawByteCollisionTargets.pred Q) emptyTable run.1)
    (hvalid : ∀ i, i < 33 → LiteralTranscript.valid i (run.2.1.2 i))
    (n c : Nat) (hn : n < 33) (hc : c < 33) (hle : c ≤ n) :
    let fc := RawCutWordsFromView.frame decoder H run.2.1.1 run.2.1.2 c
    let fn := RawCutWordsFromView.frame decoder H run.2.1.1 run.2.1.2 n
    Before run.1 fc fn ∨ fc = fn := by
  classical
  let frame := fun i => RawCutWordsFromView.frame decoder H run.2.1.1 run.2.1.2 i
  have horder := RWireRawCutLiteralAllFrames.all_adjacent_frame_order decoder d prover H run
    hrun iv Q hQ hout hvalid
  have hadj : ∀ i, i < 32 → Before run.1 (frame i) (frame (i + 1)) := by
    intro i hi
    simpa [frame] using horder i hi
  by_cases heq : c = n
  · subst c
    right
    rfl
  · left
    have hlt : c < n := by omega
    have hchain := before_n_steps run.1 frame 32 hadj (n - c) c (by omega) (by omega)
    have hcn : c + (n - c) = n := Nat.add_sub_of_le hle
    simpa [frame, hcn] using hchain

private theorem c1_raw_map_eq_current_table
    (iv : State) (H : Bytes → State) (tr : List (Bytes × State)) (Q : Nat)
    (hcons : ∀ q ∈ tr, q.2 = H q.1) (hQ : firstReads emptyTable tr ≤ Q)
    (hout : ¬ hitsBad (AllAddressCollision.bad iv BinRawByteCollisionTargets.pred Q) emptyTable tr)
    (current commitment : Bytes) (root : State)
    (hc : Before tr commitment current ∨ commitment = current)
    (hreadCurrent : Read tr current) (hreadCommit : Read tr commitment)
    (hpred : BinRawByteCollisionTargets.pred 2 commitment = some root) :
    BinCanonicalCutWords.fullC1Map tr root = tableC1Map tr current root := by
  have htable := recover_current_table_eq_full iv H tr Q hcons hQ hout current commitment root
    0x71 480 2 hreadCurrent hreadCommit hpred hc
  funext leaf
  change (BinRawByteCutStability.recoverAt 0x71 480 tr (BinMultiproof.slots 18 leaf.val) root).map Prod.fst =
    (recoverFromTable (tableBefore emptyTable tr current) 0x71 480
      (BinMultiproof.slots 18 leaf.val) root).map Prod.fst
  exact (congrArg (Option.map Prod.fst)
    (congrFun htable (BinMultiproof.slots 18 leaf.val))).symm
private theorem c2_raw_map_eq_current_table
    (iv : State) (H : Bytes → State) (tr : List (Bytes × State)) (Q : Nat)
    (hcons : ∀ q ∈ tr, q.2 = H q.1) (hQ : firstReads emptyTable tr ≤ Q)
    (hout : ¬ hitsBad (AllAddressCollision.bad iv BinRawByteCollisionTargets.pred Q) emptyTable tr)
    (current commitment : Bytes) (root : State)
    (hc : Before tr commitment current ∨ commitment = current)
    (hreadCurrent : Read tr current) (hreadCommit : Read tr commitment)
    (hpred : BinRawByteCollisionTargets.pred 2 commitment = some root) :
    BinCanonicalCutWords.fullC2Map tr root = tableC2Map tr current root := by
  have htable := recover_current_table_eq_full iv H tr Q hcons hQ hout current commitment root
    0xf1 128 2 hreadCurrent hreadCommit hpred hc
  funext leaf
  change (BinRawByteCutStability.recoverAt 0xf1 128 tr (BinMultiproof.slots 18 leaf.val) root).map Prod.fst =
    (recoverFromTable (tableBefore emptyTable tr current) 0xf1 128
      (BinMultiproof.slots 18 leaf.val) root).map Prod.fst
  exact (congrArg (Option.map Prod.fst)
    (congrFun htable (BinMultiproof.slots 18 leaf.val))).symm
private theorem folded_raw_map_eq_current_table
    (iv : State) (H : Bytes → State) (tr : List (Bytes × State)) (Q : Nat)
    (hcons : ∀ q ∈ tr, q.2 = H q.1) (hQ : firstReads emptyTable tr ≤ Q)
    (hout : ¬ hitsBad (AllAddressCollision.bad iv BinRawByteCollisionTargets.pred Q) emptyTable tr)
    (current commitment : Bytes) (root : State)
    (hc : Before tr commitment current ∨ commitment = current)
    (hreadCurrent : Read tr current) (hreadCommit : Read tr commitment)
    (hpred : BinRawByteCollisionTargets.pred 3 commitment = some root) :
    BinCanonicalCutWords.fullFoldedMap tr root = tableFoldedMap tr current root := by
  have htable := recover_current_table_eq_full iv H tr Q hcons hQ hout current commitment root
    0x72 128 3 hreadCurrent hreadCommit hpred hc
  funext leaf
  change (BinRawByteCutStability.recoverAt 0x72 128 tr (BinMultiproof.slots 18 leaf.val) root).map Prod.fst =
    (recoverFromTable (tableBefore emptyTable tr current) 0x72 128
      (BinMultiproof.slots 18 leaf.val) root).map Prod.fst
  exact (congrArg (Option.map Prod.fst)
    (congrFun htable (BinMultiproof.slots 18 leaf.val))).symm
/-- The C1 component can be reconstructed from the current table at every
row n ≥ 0, since its commitment is row 0. -/
theorem actual_c1_map_eq_current_table
    (decoder : LiteralByteProtocol.Decoder)
    (d : RawCutTranscriptRun.ErasedPrefix → RawCutTranscriptRun.ErasedMessage → Bool)
    (prover : Prover) (H : Bytes → State) (run : RawCutProverCompiler.RunView)
    (hrun : run = eval H (experiment prover (verifier decoder d)))
    (iv : State) (Q : Nat)
    (hQ : firstReads emptyTable run.1 ≤ Q)
    (hout : ¬ hitsBad (AllAddressCollision.bad iv BinRawByteCollisionTargets.pred Q) emptyTable run.1)
    (hvalid : ∀ i, i < 33 → LiteralTranscript.valid i (run.2.1.2 i))
    (n : Nat) (hn : n < 33) (h0le : 0 ≤ n)
    (root : State) (word : LiteralTranscript.C1Word)
    (h0 : run.2.1.2 0 = .initial root word) :
    BinCanonicalCutWords.fullC1Map run.1 root = tableC1Map run.1
      (RawCutWordsFromView.frame decoder H run.2.1.1 run.2.1.2 n) root := by
  let current := RawCutWordsFromView.frame decoder H run.2.1.1 run.2.1.2 n
  let commit := RawCutWordsFromView.frame decoder H run.2.1.1 run.2.1.2 0
  have hcons : ∀ q ∈ run.1, q.2 = H q.1 := by rw [hrun]; exact FS.eval_consistent H _
  have hc : Before run.1 commit current ∨ commit = current := by
    simpa [commit, current] using actual_frame_order_or_eq decoder d prover H run hrun iv Q hQ hout hvalid n 0 hn (by decide) h0le
  have hreadCurrent : Read run.1 current := by
    change Read run.1 (RawCutWordsFromView.frame decoder H run.2.1.1 run.2.1.2 n)
    rw [hrun]
    exact RawCutWordsFromView.frame_read decoder d prover H n hn
  have hreadCommit : Read run.1 commit := by
    change Read run.1 (RawCutWordsFromView.frame decoder H run.2.1.1 run.2.1.2 0)
    rw [hrun]
    exact RawCutWordsFromView.frame_read decoder d prover H 0 (by decide)
  have hpred : BinRawByteCollisionTargets.pred 2 commit = some root := by
    change BinRawByteCollisionTargets.pred 2
      (RawCutWordsFromView.frame decoder H run.2.1.1 run.2.1.2 0) = some root
    exact RWireConstructedWords.initial_root decoder H run.2.1.1 run.2.1.2 root word h0
  exact c1_raw_map_eq_current_table iv H run.1 Q hcons hQ hout current commit root hc
    hreadCurrent hreadCommit hpred

/-- The C2 component can be reconstructed from the current table at every
row n ≥ 2, after its typed payload has supplied the commitment root. -/
theorem actual_c2_map_eq_current_table
    (decoder : LiteralByteProtocol.Decoder)
    (d : RawCutTranscriptRun.ErasedPrefix → RawCutTranscriptRun.ErasedMessage → Bool)
    (prover : Prover) (H : Bytes → State) (run : RawCutProverCompiler.RunView)
    (hrun : run = eval H (experiment prover (verifier decoder d)))
    (iv : State) (Q : Nat)
    (hQ : firstReads emptyTable run.1 ≤ Q)
    (hout : ¬ hitsBad (AllAddressCollision.bad iv BinRawByteCollisionTargets.pred Q) emptyTable run.1)
    (hvalid : ∀ i, i < 33 → LiteralTranscript.valid i (run.2.1.2 i))
    (n : Nat) (hn : n < 33) (h2le : 2 ≤ n)
    (root : State) (msg : LiteralTranscript.BytesMessage) (word : LiteralTranscript.C2Word)
    (h2 : run.2.1.2 2 = .c2 msg word)
    (hdecode : SemanticRecordCodec.decode ⟨2, by decide⟩ msg.val =
      some ⟨.c2Root root, by rfl⟩) :
    BinCanonicalCutWords.fullC2Map run.1 root = tableC2Map run.1
      (RawCutWordsFromView.frame decoder H run.2.1.1 run.2.1.2 n) root := by
  let current := RawCutWordsFromView.frame decoder H run.2.1.1 run.2.1.2 n
  let commit := RawCutWordsFromView.frame decoder H run.2.1.1 run.2.1.2 2
  have hcons : ∀ q ∈ run.1, q.2 = H q.1 := by rw [hrun]; exact FS.eval_consistent H _
  have hc : Before run.1 commit current ∨ commit = current := by
    simpa [commit, current] using actual_frame_order_or_eq decoder d prover H run hrun iv Q hQ hout hvalid n 2 hn (by decide) h2le
  have hreadCurrent : Read run.1 current := by
    change Read run.1 (RawCutWordsFromView.frame decoder H run.2.1.1 run.2.1.2 n)
    rw [hrun]
    exact RawCutWordsFromView.frame_read decoder d prover H n hn
  have hreadCommit : Read run.1 commit := by
    change Read run.1 (RawCutWordsFromView.frame decoder H run.2.1.1 run.2.1.2 2)
    rw [hrun]
    exact RawCutWordsFromView.frame_read decoder d prover H 2 (by decide)
  have hpred : BinRawByteCollisionTargets.pred 2 commit = some root := by
    change BinRawByteCollisionTargets.pred 2
      (RawCutWordsFromView.frame decoder H run.2.1.1 run.2.1.2 2) = some root
    exact RWireConstructedWords.c2_root decoder H run.2.1.1 run.2.1.2 msg word root h2 hdecode
  exact c2_raw_map_eq_current_table iv H run.1 Q hcons hQ hout current commit root hc
    hreadCurrent hreadCommit hpred

/-- The folded component can be reconstructed from the current table at every
row n ≥ 30, after the second-opening parser supplies its root. -/
theorem actual_folded_map_eq_current_table
    (decoder : LiteralByteProtocol.Decoder)
    (d : RawCutTranscriptRun.ErasedPrefix → RawCutTranscriptRun.ErasedMessage → Bool)
    (prover : Prover) (H : Bytes → State) (run : RawCutProverCompiler.RunView)
    (hrun : run = eval H (experiment prover (verifier decoder d)))
    (iv : State) (Q : Nat)
    (hQ : firstReads emptyTable run.1 ≤ Q)
    (hout : ¬ hitsBad (AllAddressCollision.bad iv BinRawByteCollisionTargets.pred Q) emptyTable run.1)
    (hvalid : ∀ i, i < 33 → LiteralTranscript.valid i (run.2.1.2 i))
    (n : Nat) (hn : n < 33) (h30le : 30 ≤ n)
    (msg : LiteralTranscript.BytesMessage) (word : LiteralTranscript.VWord)
    (payload : OpeningRecordCodec.Payload .second)
    (h30 : run.2.1.2 30 = .second msg word)
    (hdecode : OpeningRecordCodec.decode .second msg.val = some payload) :
    BinCanonicalCutWords.fullFoldedMap run.1 payload.1 = tableFoldedMap run.1
      (RawCutWordsFromView.frame decoder H run.2.1.1 run.2.1.2 n) payload.1 := by
  let current := RawCutWordsFromView.frame decoder H run.2.1.1 run.2.1.2 n
  let commit := RawCutWordsFromView.frame decoder H run.2.1.1 run.2.1.2 30
  have hcons : ∀ q ∈ run.1, q.2 = H q.1 := by rw [hrun]; exact FS.eval_consistent H _
  have hc : Before run.1 commit current ∨ commit = current := by
    simpa [commit, current] using actual_frame_order_or_eq decoder d prover H run hrun iv Q hQ hout hvalid n 30 hn (by decide) h30le
  have hreadCurrent : Read run.1 current := by
    change Read run.1 (RawCutWordsFromView.frame decoder H run.2.1.1 run.2.1.2 n)
    rw [hrun]
    exact RawCutWordsFromView.frame_read decoder d prover H n hn
  have hreadCommit : Read run.1 commit := by
    change Read run.1 (RawCutWordsFromView.frame decoder H run.2.1.1 run.2.1.2 30)
    rw [hrun]
    exact RawCutWordsFromView.frame_read decoder d prover H 30 (by decide)
  have hpred : BinRawByteCollisionTargets.pred 3 commit = some payload.1 := by
    change BinRawByteCollisionTargets.pred 3
      (RawCutWordsFromView.frame decoder H run.2.1.1 run.2.1.2 30) = some payload.1
    exact RWireConstructedWords.second_root decoder H run.2.1.1 run.2.1.2 msg word payload h30 hdecode
  exact folded_raw_map_eq_current_table iv H run.1 Q hcons hQ hout current commit payload.1 hc
    hreadCurrent hreadCommit hpred

#print axioms recover_current_table_eq_full
#print axioms actual_c1_map_eq_current_table
#print axioms actual_c2_map_eq_current_table
#print axioms actual_folded_map_eq_current_table
#print axioms before_n_steps
#print axioms actual_frame_order_or_eq
#print axioms c1_raw_map_eq_current_table
#print axioms c2_raw_map_eq_current_table
#print axioms folded_raw_map_eq_current_table
end AspisR1.RWireRawCutLaterTableLiteralWords
end
