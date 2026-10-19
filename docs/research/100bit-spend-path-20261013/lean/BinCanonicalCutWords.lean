import BinRawByteCutStability
import BinMultiproof
import CanonicalCutEnrichedTranscript

/-! Binary packed maps, reusing the arity-independent typed projections and
word metadata of CanonicalCutEnrichedTranscript.lean:30-44. Folded leaves
remain padded in the same 18-level commitment domain (candidate.rs:111).
No large finite domain is evaluated. -/
set_option autoImplicit false
namespace AspisR1.BinCanonicalCutWords
open FS FS2 FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.AdaptiveFirstReadLaw
open CanonicalCutEnrichedTranscript (Words wordsFromMaps)
open BinMerkle32Path

def rawC1Map (tr : List (Bytes × State)) (frame : Bytes) (root : State) :
    Fin 262144 → Option (List Byte) := fun leaf =>
  (BinRawByteCutStability.recoverAt 0x71 480
    (BinRawByteCutRecovery.cut tr frame)
    (BinMultiproof.slots 18 leaf.val) root).map Prod.fst

def rawC2Map (tr : List (Bytes × State)) (frame : Bytes) (root : State) :
    Fin 262144 → Option (List Byte) := fun leaf =>
  (BinRawByteCutStability.recoverAt 0xf1 128
    (BinRawByteCutRecovery.cut tr frame)
    (BinMultiproof.slots 18 leaf.val) root).map Prod.fst

def rawFoldedMap (tr : List (Bytes × State)) (frame : Bytes) (root : State) :
    Fin 65536 → Option (List Byte) := fun leaf =>
  (BinRawByteCutStability.recoverAt 0x72 128
    (BinRawByteCutRecovery.cut tr frame)
    (BinMultiproof.slots 18 leaf.val) root).map Prod.fst

/-- The ideal typed words are assembled from the recovered maps at the three
actual commitment cuts. The concrete frames are caller-provided here so the
source-level frame constructors can be instantiated without adding length
premises to the recovery API. -/
def wordsFromRawCuts (tr : List (Bytes × State))
    (c1Frame c2Frame foldedFrame : Bytes) (c1Root c2Root foldedRoot : State) : Words :=
  wordsFromMaps (rawC1Map tr c1Frame c1Root) (rawC2Map tr c2Frame c2Root)
    (rawFoldedMap tr foldedFrame foldedRoot)

/-- The concrete literal commitment-frame shapes. The caller supplies the
public bytes, prefix states, roots and folded tail already selected by the
transcript; this definition only instantiates the retained frame constructors. -/
def wordsFromCommitmentFrames (tr : List (Bytes × State))
    (pubBytes : Bytes) (c1Root c2State c2Root foldedState foldedRoot : State)
    (foldedTail : Bytes) : Words :=
  wordsFromRawCuts tr
    (PublicInitFrame.pre pubBytes ++ AspisV8R19.SourceDuplexStep.bytes c1Root)
    (CommitmentRootFrames.c2Frame c2State c2Root)
    (CommitmentRootFrames.foldedFrame foldedState foldedRoot foldedTail)
    c1Root c2Root foldedRoot

/-- Full-log packed maps for comparison with the first-read cut maps. -/
def fullC1Map (tr : List (Bytes × State)) (root : State) :
    Fin 262144 → Option (List Byte) := fun leaf =>
  (BinRawByteCutStability.recoverAt 0x71 480 tr
    (BinMultiproof.slots 18 leaf.val) root).map Prod.fst

def fullC2Map (tr : List (Bytes × State)) (root : State) :
    Fin 262144 → Option (List Byte) := fun leaf =>
  (BinRawByteCutStability.recoverAt 0xf1 128 tr
    (BinMultiproof.slots 18 leaf.val) root).map Prod.fst

def fullFoldedMap (tr : List (Bytes × State)) (root : State) :
    Fin 65536 → Option (List Byte) := fun leaf =>
  (BinRawByteCutStability.recoverAt 0x72 128 tr
    (BinMultiproof.slots 18 leaf.val) root).map Prod.fst

/-- One raw-byte collision exclusion makes the C1, C2, and folded packed maps
at their commitment frames equal to the corresponding full-log maps. -/
theorem wordsFromRawCuts_eq_full
    (iv : State) (H : Bytes → State) (tr : List (Bytes × State)) (Q : Nat)
    (hcons : ∀ q ∈ tr, q.2 = H q.1)
    (hQ : firstReads emptyTable tr ≤ Q)
    (hout : ¬ hitsBad (AllAddressCollision.bad iv BinRawByteCollisionTargets.pred Q)
      emptyTable tr)
    (c1Frame c2Frame foldedFrame : Bytes)
    (c1Root c2Root foldedRoot : State)
    (j1 j2 j3 : Fin 5)
    (hc1frame : Read tr c1Frame)
    (hc2frame : Read tr c2Frame)
    (hfoldedframe : Read tr foldedFrame)
    (hc1pred : BinRawByteCollisionTargets.pred j1 c1Frame = some c1Root)
    (hc2pred : BinRawByteCollisionTargets.pred j2 c2Frame = some c2Root)
    (hfoldedpred : BinRawByteCollisionTargets.pred j3 foldedFrame = some foldedRoot) :
    wordsFromRawCuts tr c1Frame c2Frame foldedFrame c1Root c2Root foldedRoot =
      wordsFromMaps (fullC1Map tr c1Root) (fullC2Map tr c2Root)
        (fullFoldedMap tr foldedRoot) := by
  have hc1 := BinRawByteCutStability.all_paths_stable iv H tr Q hcons hQ hout
    0x71 480 c1Root c1Frame j1 hc1frame hc1pred
  have hc2 := BinRawByteCutStability.all_paths_stable iv H tr Q hcons hQ hout
    0xf1 128 c2Root c2Frame j2 hc2frame hc2pred
  have hfolded := BinRawByteCutStability.all_paths_stable iv H tr Q hcons hQ hout
    0x72 128 foldedRoot foldedFrame j3 hfoldedframe hfoldedpred
  have hc1map : rawC1Map tr c1Frame c1Root = fullC1Map tr c1Root := by
    funext leaf
    unfold rawC1Map fullC1Map
    exact congrArg (fun x => x.map Prod.fst)
      (congrFun hc1 (BinMultiproof.slots 18 leaf.val))
  have hc2map : rawC2Map tr c2Frame c2Root = fullC2Map tr c2Root := by
    funext leaf
    unfold rawC2Map fullC2Map
    exact congrArg (fun x => x.map Prod.fst)
      (congrFun hc2 (BinMultiproof.slots 18 leaf.val))
  have hfoldedmap : rawFoldedMap tr foldedFrame foldedRoot = fullFoldedMap tr foldedRoot := by
    funext leaf
    unfold rawFoldedMap fullFoldedMap
    exact congrArg (fun x => x.map Prod.fst)
      (congrFun hfolded (BinMultiproof.slots 18 leaf.val))
  simp [wordsFromRawCuts, hc1map, hc2map, hfoldedmap]


#print axioms wordsFromRawCuts_eq_full
end AspisR1.BinCanonicalCutWords
