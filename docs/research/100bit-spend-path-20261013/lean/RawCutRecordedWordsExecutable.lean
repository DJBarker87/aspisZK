import CanonicalCutEnrichedTranscript
import RawByteCutRecovery
import RawByteCollisionTargets

set_option autoImplicit false
namespace AspisR1.RawCutRecordedWordsExecutable

open FS FS2 FS2.Duplex AspisR1
open AspisR1.CanonicalCutEnrichedTranscript
open AspisR1.MerkleTable AspisR1.MerkleRecordedLog AspisR1.MerkleLeafRecovery
open AspisR1.MerkleIndexGeometry AspisR1.RawByteCutRecovery
open Merkle32Path Merkle32Leaf

abbrev Byte := AspisR1.ExactLeafFieldCodec.Byte
abbrev Bytes := AspisV8R19.DuplexFrames.Bytes
abbrev State := AspisV8R19.SourceDuplexStep.State

/-- Executable spelling of the first-occurrence index used by the recorded
cut.  The proof wrapper in FS2.Duplex is declared in a noncomputable section;
this structurally identical recursion is available to the runtime. -/
def firstIndexExec {I A : Type} [DecidableEq I] (a : I) : List (I × A) → Nat
  | [] => 0
  | (i, _) :: rest => if i = a then 0 else firstIndexExec a rest + 1

theorem firstIndexExec_eq_firstIdx {I A : Type} [DecidableEq I]
    (a : I) (tr : List (I × A)) : firstIndexExec a tr = FS2.Duplex.firstIdx a tr := by
  induction tr with
  | nil => rfl
  | cons q rest ih =>
      rcases q with ⟨i, v⟩
      by_cases h : i = a <;> simp [firstIndexExec, FS2.Duplex.firstIdx, h, ih]

/-- Executable prefix ending immediately before the first recorded frame. -/
def cutBeforeExec (tr : List (Bytes × State)) (frame : Bytes) : List (Bytes × State) :=
  tr.take (firstIndexExec frame tr)

theorem cutBeforeExec_eq_cut (tr : List (Bytes × State)) (frame : Bytes) :
    cutBeforeExec tr frame = RawByteCutRecovery.cut tr frame := by
  simp only [cutBeforeExec, RawByteCutRecovery.cut]
  rw [firstIndexExec_eq_firstIdx]

/-- Deterministic recorded-log recovery, inlined rather than routed through the
noncomputable stability wrapper. -/
def recoverAtExec (tag : Merkle32Path.Byte) (width : Nat)
    (log : AspisR1.MerkleRecordedLog.Log) (slots : List (Fin 8)) (root : State) :
    Option AspisR1.MerkleLeafRecovery.LeafData :=
  MerkleLeafRecovery.recover (MerkleRecordedLog.nodes log)
    (MerkleRecordedLog.leaves tag width log) slots root

theorem recoverAtExec_eq_recoverAt (tag : Merkle32Path.Byte) (width : Nat)
    (log : AspisR1.MerkleRecordedLog.Log) (slots : List (Fin 8)) (root : State) :
    recoverAtExec tag width log slots root =
      MerkleLeafRecovery.recover (MerkleRecordedLog.nodes log)
        (MerkleRecordedLog.leaves tag width log) slots root := rfl

def c1MapExec (tr : List (Bytes × State)) (frame : Bytes) (root : State) :
    Fin 262144 → Option (List Byte) := fun leaf =>
  (recoverAtExec 0x71 480 (cutBeforeExec tr frame)
    (MerkleIndexGeometry.slots 6 leaf.val) root).map Prod.fst

def c2MapExec (tr : List (Bytes × State)) (frame : Bytes) (root : State) :
    Fin 262144 → Option (List Byte) := fun leaf =>
  (recoverAtExec 0xf1 128 (cutBeforeExec tr frame)
    (MerkleIndexGeometry.slots 6 leaf.val) root).map Prod.fst

def foldedMapExec (tr : List (Bytes × State)) (frame : Bytes) (root : State) :
    Fin 65536 → Option (List Byte) := fun leaf =>
  (recoverAtExec 0x72 128 (cutBeforeExec tr frame)
    (MerkleIndexGeometry.slots 6 leaf.val) root).map Prod.fst

/-- Assemble typed C1, C2, and folded words from three recorded-log cuts.
The operation consists only of finite list parsing, Merkle path lookup,
strict leaf decoding, and the existing zero-default projections. -/
def wordsFromRecordedCutsExec (tr : List (Bytes × State))
    (c1Frame c2Frame foldedFrame : Bytes) (c1Root c2Root foldedRoot : State) :
    Words :=
  wordsFromMaps (c1MapExec tr c1Frame c1Root) (c2MapExec tr c2Frame c2Root)
    (foldedMapExec tr foldedFrame foldedRoot)

theorem c1MapExec_eq_raw (tr : List (Bytes × State)) (frame : Bytes) (root : State) :
    c1MapExec tr frame root = CanonicalCutEnrichedTranscript.rawC1Map tr frame root := by
  funext leaf
  simp [c1MapExec, CanonicalCutEnrichedTranscript.rawC1Map, recoverAtExec,
    AspisR1.RawByteCutStability.recoverAt, cutBeforeExec_eq_cut]

theorem c2MapExec_eq_raw (tr : List (Bytes × State)) (frame : Bytes) (root : State) :
    c2MapExec tr frame root = CanonicalCutEnrichedTranscript.rawC2Map tr frame root := by
  funext leaf
  simp [c2MapExec, CanonicalCutEnrichedTranscript.rawC2Map, recoverAtExec,
    AspisR1.RawByteCutStability.recoverAt, cutBeforeExec_eq_cut]

theorem foldedMapExec_eq_raw (tr : List (Bytes × State)) (frame : Bytes) (root : State) :
    foldedMapExec tr frame root = CanonicalCutEnrichedTranscript.rawFoldedMap tr frame root := by
  funext leaf
  simp [foldedMapExec, CanonicalCutEnrichedTranscript.rawFoldedMap, recoverAtExec,
    AspisR1.RawByteCutStability.recoverAt, cutBeforeExec_eq_cut]

theorem wordsFromRecordedCutsExec_eq_wordsFromRawCuts
    (tr : List (Bytes × State)) (c1Frame c2Frame foldedFrame : Bytes)
    (c1Root c2Root foldedRoot : State) :
    wordsFromRecordedCutsExec tr c1Frame c2Frame foldedFrame c1Root c2Root foldedRoot =
      CanonicalCutEnrichedTranscript.wordsFromRawCuts tr c1Frame c2Frame foldedFrame
        c1Root c2Root foldedRoot := by
  unfold wordsFromRecordedCutsExec CanonicalCutEnrichedTranscript.wordsFromRawCuts
  rw [c1MapExec_eq_raw, c2MapExec_eq_raw, foldedMapExec_eq_raw]

/-- Runtime root selection used by the recorded-view constructor. -/
def rootFromExec (j : Fin 11) (input : Bytes) : State :=
  (RawByteCollisionTargets.pred j input).getD default

def wordsFromRecordedLogExec (tr : List (Bytes × State))
    (c1Frame c2Frame foldedFrame : Bytes) : Words :=
  wordsFromRecordedCutsExec tr c1Frame c2Frame foldedFrame
    (rootFromExec 8 c1Frame) (rootFromExec 8 c2Frame) (rootFromExec 9 foldedFrame)

theorem wordsFromRecordedLogExec_eq_wordsFromRawCuts
    (tr : List (Bytes × State)) (c1Frame c2Frame foldedFrame : Bytes) :
    wordsFromRecordedLogExec tr c1Frame c2Frame foldedFrame =
      CanonicalCutEnrichedTranscript.wordsFromRawCuts tr c1Frame c2Frame foldedFrame
        (rootFromExec 8 c1Frame) (rootFromExec 8 c2Frame)
        (rootFromExec 9 foldedFrame) := by
  exact wordsFromRecordedCutsExec_eq_wordsFromRawCuts tr c1Frame c2Frame foldedFrame
    (rootFromExec 8 c1Frame) (rootFromExec 8 c2Frame) (rootFromExec 9 foldedFrame)

#print axioms firstIndexExec_eq_firstIdx
#print axioms cutBeforeExec_eq_cut
#print axioms wordsFromRecordedCutsExec_eq_wordsFromRawCuts
#print axioms wordsFromRecordedLogExec_eq_wordsFromRawCuts
end AspisR1.RawCutRecordedWordsExecutable
