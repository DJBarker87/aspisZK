import RawCutRecordedWordsExecutable
import BinCanonicalCutWords
import BinSharedGrammarBridge
import BinLeafBoundedTable

set_option autoImplicit false
namespace AspisR1.RawCutRecordedWordsBoundedBin
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open CanonicalCutEnrichedTranscript (Words wordsFromMaps)
abbrev Byte := BinMerkle32Path.Byte
abbrev cutBeforeExec := RawCutRecordedWordsExecutable.cutBeforeExec

theorem cutBeforeExec_eq_cut (tr : List (Bytes × State)) (frame : Bytes) :
    cutBeforeExec tr frame = BinRawByteCutRecovery.cut tr frame :=
  RawCutRecordedWordsExecutable.cutBeforeExec_eq_cut tr frame

/-- Recovery uses the bounded leaf parser at every table occurrence. -/
def recoverAtExec (tag : BinMerkle32Path.Byte) (width : Nat)
    (log : AspisR1.BinMerkleRecordedLog.Log) (slots : List (Fin 2)) (root : State) :
    Option AspisR1.BinMerkleLeafRecovery.LeafData :=
  BinMerkleLeafRecovery.recover (BinMerkleRecordedLog.nodes log)
    ((BinLeafBoundedTable.leaves tag width log).1) slots root

theorem recoverAtExec_eq_recoverAt (tag : BinMerkle32Path.Byte) (width : Nat)
    (log : AspisR1.BinMerkleRecordedLog.Log) (slots : List (Fin 2)) (root : State) :
    recoverAtExec tag width log slots root =
      BinMerkleLeafRecovery.recover (BinMerkleRecordedLog.nodes log)
        (BinMerkleRecordedLog.leaves tag width log) slots root := by
  exact congrArg (fun leaves => BinMerkleLeafRecovery.recover
    (BinMerkleRecordedLog.nodes log) leaves slots root)
    (BinLeafBoundedTable.leaves_value tag width log)

def c1MapExec (tr : List (Bytes × State)) (frame : Bytes) (root : State) :
    Fin 262144 → Option (List Byte) := fun leaf =>
  (recoverAtExec 0x71 480 (cutBeforeExec tr frame)
    (BinMultiproof.slots 18 leaf.val) root).map Prod.fst

def c2MapExec (tr : List (Bytes × State)) (frame : Bytes) (root : State) :
    Fin 262144 → Option (List Byte) := fun leaf =>
  (recoverAtExec 0xf1 128 (cutBeforeExec tr frame)
    (BinMultiproof.slots 18 leaf.val) root).map Prod.fst

def foldedMapExec (tr : List (Bytes × State)) (frame : Bytes) (root : State) :
    Fin 65536 → Option (List Byte) := fun leaf =>
  (recoverAtExec 0x72 128 (cutBeforeExec tr frame)
    (BinMultiproof.slots 18 leaf.val) root).map Prod.fst

/-- Assemble typed C1, C2, and folded words from three recorded-log cuts.
The operation consists only of finite list parsing, Merkle path lookup,
strict leaf decoding, and the existing zero-default projections. -/
def wordsFromRecordedCutsExec (tr : List (Bytes × State))
    (c1Frame c2Frame foldedFrame : Bytes) (c1Root c2Root foldedRoot : State) :
    Words :=
  wordsFromMaps (c1MapExec tr c1Frame c1Root) (c2MapExec tr c2Frame c2Root)
    (foldedMapExec tr foldedFrame foldedRoot)

theorem c1MapExec_eq_raw (tr : List (Bytes × State)) (frame : Bytes) (root : State) :
    c1MapExec tr frame root = BinCanonicalCutWords.rawC1Map tr frame root := by
  funext leaf
  simp [c1MapExec, BinCanonicalCutWords.rawC1Map, recoverAtExec,
    AspisR1.BinRawByteCutStability.recoverAt, cutBeforeExec_eq_cut,
    BinLeafBoundedTable.leaves_value]

theorem c2MapExec_eq_raw (tr : List (Bytes × State)) (frame : Bytes) (root : State) :
    c2MapExec tr frame root = BinCanonicalCutWords.rawC2Map tr frame root := by
  funext leaf
  simp [c2MapExec, BinCanonicalCutWords.rawC2Map, recoverAtExec,
    AspisR1.BinRawByteCutStability.recoverAt, cutBeforeExec_eq_cut,
    BinLeafBoundedTable.leaves_value]

theorem foldedMapExec_eq_raw (tr : List (Bytes × State)) (frame : Bytes) (root : State) :
    foldedMapExec tr frame root = BinCanonicalCutWords.rawFoldedMap tr frame root := by
  funext leaf
  simp [foldedMapExec, BinCanonicalCutWords.rawFoldedMap, recoverAtExec,
    AspisR1.BinRawByteCutStability.recoverAt, cutBeforeExec_eq_cut,
    BinLeafBoundedTable.leaves_value]

theorem wordsFromRecordedCutsExec_eq_wordsFromRawCuts
    (tr : List (Bytes × State)) (c1Frame c2Frame foldedFrame : Bytes)
    (c1Root c2Root foldedRoot : State) :
    wordsFromRecordedCutsExec tr c1Frame c2Frame foldedFrame c1Root c2Root foldedRoot =
      BinCanonicalCutWords.wordsFromRawCuts tr c1Frame c2Frame foldedFrame
        c1Root c2Root foldedRoot := by
  unfold wordsFromRecordedCutsExec BinCanonicalCutWords.wordsFromRawCuts
  rw [c1MapExec_eq_raw, c2MapExec_eq_raw, foldedMapExec_eq_raw]


#print axioms cutBeforeExec_eq_cut
#print axioms recoverAtExec_eq_recoverAt
#print axioms c1MapExec_eq_raw
#print axioms c2MapExec_eq_raw
#print axioms foldedMapExec_eq_raw
#print axioms wordsFromRecordedCutsExec_eq_wordsFromRawCuts
end AspisR1.RawCutRecordedWordsBoundedBin
