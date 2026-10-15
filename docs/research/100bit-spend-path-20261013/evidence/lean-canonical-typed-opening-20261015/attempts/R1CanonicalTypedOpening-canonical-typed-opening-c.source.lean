import R1ThreeCommitmentFullTrace
import R1TypedRecoveryStability
import R1FoldedRecoveredWord
import R1MixedLeafDecoder

/-! Strictly decode accepted C1, C2, and folded leaves after composing the
existing no-event recovery theorem with its later-of-earlier extension. The
six-level path specialization is a representation choice, not a Rust/source
refinement theorem. -/
set_option autoImplicit false

namespace AspisR1.CanonicalTypedOpening

open FS FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open AspisV8PairedCommitment
open Merkle32Path Merkle32Leaf MerkleTable MerkleLeafRecovery MerkleRecordedLog
open AspisR1.CanonicalRecoveryStability
open AspisR1.ThreeCommitmentFullTrace
open AspisR1.TypedRecoveryStability
open AspisR1.TypedRecoveredWords
open AspisR1.FoldedLeafCodec
open AspisR1.FoldedRecoveredWord
open AspisR1.MerkleIndexGeometry
open AspisR1.MixedLeafDecoder
open AspisR1.CanonicalByteHash
open AspisR1.CanonicalFullTraceRecovery

variable {M Cv : Type} {L : Nat}

def paths6C1C2 : Fin 262144 → List (Fin 8) :=
  fun leaf => MerkleIndexGeometry.slots 6 leaf.val

def paths6Folded : Fin 65536 → List (Fin 8) :=
  fun leaf => MerkleIndexGeometry.slots 6 leaf.val

theorem c1_decode_of_no_events (p : Params M Cv L) (Qtot : Nat)
    (H : Addr L → State) (pre post : List (Addr L × State))
    (hcons : ∀ q ∈ pre ++ post, q.2 = H q.1)
    (pubBytes : Bytes) (hframe : 75 + pubBytes.length ≤ L)
    (hsize : 514 ≤ L) (hnode : 257 ≤ L)
    (packed salt : List AspisR1.ExactLeafFieldCodec.Byte)
    (hw : packed.length = 480) (hs : salt.length = 32)
    (leaf : Fin 262144)
    (path : Path (MerkleIndexGeometry.slots 6 leaf.val)) (root : State)
    (hcommit : Read pre (PublicInitFrame.addr pubBytes hframe root))
    (haccept : (eval H (CanonicalMerkleProgram.program path
      (leafInput 0x71 packed salt))).2 = root)
    (hopen : ∀ a, Read (eval H (CanonicalMerkleProgram.program path
      (leafInput 0x71 packed salt))).1 a → Read (pre ++ post) a)
    (hQ : firstReads emptyTable (pre ++ post) ≤ Qtot)
    (hnoColl : ¬ hitsBad (badColl p Qtot) emptyTable (pre ++ post))
    (hnoChild : ¬ hitsBad (ParsedTargetsCollision.bad MerkleChildTargets.pred Qtot)
      emptyTable (pre ++ post))
    (hnoRoot : ¬ hitsBad
      (ParsedTargetsCollision.bad CommitmentRootTargets.pred Qtot) emptyTable
      (pre ++ post))
    (payload : C1) (hdecode : decodeC1 packed = some payload) :
    decodeC1At (c1PackedAt (pre ++ post) paths6C1C2 root) leaf = some payload := by
  have hbefore : recoverAt 0x71 480 pre
      (MerkleIndexGeometry.slots 6 leaf.val) root = some (packed, salt) := by
    exact ThreeCommitmentFullTrace.c1_recover_of_no_events p Qtot H pre post hcons
      pubBytes hframe hsize hnode packed salt hw hs path root hcommit haccept hopen
      hQ hnoColl hnoChild hnoRoot
  have hfull := CanonicalRecoveryStability.later_of_earlier 0x71 480 pre post
    (MerkleIndexGeometry.slots 6 leaf.val) root (packed, salt) hbefore
  have hpacked : c1PackedAt (pre ++ post) paths6C1C2 root leaf = some packed := by
    simp [c1PackedAt, TypedRecoveryStability.packedAt, paths6C1C2, hfull]
  simp [decodeC1At, hpacked, hdecode]

#print axioms c1_decode_of_no_events

theorem c2_decode_of_no_events (p : Params M Cv L) (Qtot : Nat)
    (H : Addr L → State) (pre post : List (Addr L × State))
    (hcons : ∀ q ∈ pre ++ post, q.2 = H q.1)
    (state : State) (hframe : 71 ≤ L) (hsize : 162 ≤ L) (hnode : 257 ≤ L)
    (packed salt : List AspisR1.ExactLeafFieldCodec.Byte)
    (hw : packed.length = 128) (hs : salt.length = 32)
    (leaf : Fin 262144)
    (path : Path (MerkleIndexGeometry.slots 6 leaf.val)) (root : State)
    (hcommit : Read pre (CommitmentRootFrames.c2Addr state root hframe))
    (haccept : (eval H (CanonicalMerkleProgram.program path
      (leafInput 0xf1 packed salt))).2 = root)
    (hopen : ∀ a, Read (eval H (CanonicalMerkleProgram.program path
      (leafInput 0xf1 packed salt))).1 a → Read (pre ++ post) a)
    (hQ : firstReads emptyTable (pre ++ post) ≤ Qtot)
    (hnoColl : ¬ hitsBad (badColl p Qtot) emptyTable (pre ++ post))
    (hnoChild : ¬ hitsBad (ParsedTargetsCollision.bad MerkleChildTargets.pred Qtot)
      emptyTable (pre ++ post))
    (hnoRoot : ¬ hitsBad
      (ParsedTargetsCollision.bad CommitmentRootTargets.pred Qtot) emptyTable
      (pre ++ post))
    (payload : C2) (hdecode : decodeC2 packed = some payload) :
    decodeC2At (c2PackedAt (pre ++ post) paths6C1C2 root) leaf = some payload := by
  have hbefore : recoverAt 0xf1 128 pre
      (MerkleIndexGeometry.slots 6 leaf.val) root = some (packed, salt) := by
    exact ThreeCommitmentFullTrace.c2_recover_of_no_events p Qtot H pre post hcons
      state hframe hsize hnode packed salt hw hs path root hcommit haccept hopen
      hQ hnoColl hnoChild hnoRoot
  have hfull := CanonicalRecoveryStability.later_of_earlier 0xf1 128 pre post
    (MerkleIndexGeometry.slots 6 leaf.val) root (packed, salt) hbefore
  have hpacked : c2PackedAt (pre ++ post) paths6C1C2 root leaf = some packed := by
    simp [c2PackedAt, TypedRecoveryStability.packedAt, paths6C1C2, hfull]
  simp [decodeC2At, hpacked, hdecode]

#print axioms c2_decode_of_no_events

theorem folded_decode_of_no_events (p : Params M Cv L) (Qtot : Nat)
    (H : Addr L → State) (pre post : List (Addr L × State))
    (hcons : ∀ q ∈ pre ++ post, q.2 = H q.1)
    (state : State) (tail : Bytes) (htail : tail.length = 224)
    (hframe : 294 ≤ L) (hsize : 162 ≤ L) (hnode : 257 ≤ L)
    (packed salt : List AspisR1.ExactLeafFieldCodec.Byte)
    (hw : packed.length = 128) (hs : salt.length = 32)
    (leaf : Fin 65536)
    (path : Path (MerkleIndexGeometry.slots 6 leaf.val)) (root : State)
    (hcommit : Read pre
      (CommitmentRootFrames.foldedAddr state root tail htail hframe))
    (haccept : (eval H (CanonicalMerkleProgram.program path
      (leafInput 0x72 packed salt))).2 = root)
    (hopen : ∀ a, Read (eval H (CanonicalMerkleProgram.program path
      (leafInput 0x72 packed salt))).1 a → Read (pre ++ post) a)
    (hQ : firstReads emptyTable (pre ++ post) ≤ Qtot)
    (hnoColl : ¬ hitsBad (badColl p Qtot) emptyTable (pre ++ post))
    (hnoChild : ¬ hitsBad (ParsedTargetsCollision.bad MerkleChildTargets.pred Qtot)
      emptyTable (pre ++ post))
    (hnoRoot : ¬ hitsBad
      (ParsedTargetsCollision.bad CommitmentRootTargets.pred Qtot) emptyTable
      (pre ++ post))
    (payload : AspisR1.FoldedLeafCodec.Folded)
    (hdecode : decodeFolded packed = some payload) :
    (FoldedRecoveredWord.packedAt (pre ++ post) root leaf).bind decodeFolded =
      some payload := by
  have hbefore : recoverAt 0x72 128 pre
      (MerkleIndexGeometry.slots 6 leaf.val) root = some (packed, salt) := by
    exact ThreeCommitmentFullTrace.folded_recover_of_no_events p Qtot H pre post hcons
      state tail htail hframe hsize hnode packed salt hw hs path root hcommit haccept
      hopen hQ hnoColl hnoChild hnoRoot
  have hfull := CanonicalRecoveryStability.later_of_earlier 0x72 128 pre post
    (MerkleIndexGeometry.slots 6 leaf.val) root (packed, salt) hbefore
  have hpacked : FoldedRecoveredWord.packedAt (pre ++ post) root leaf = some packed := by
    simp [FoldedRecoveredWord.packedAt, hfull]
  simp [hpacked, hdecode]

#print axioms folded_decode_of_no_events

theorem folded_word_of_no_events (p : Params M Cv L) (Qtot : Nat)
    (H : Addr L → State) (pre post : List (Addr L × State))
    (hcons : ∀ q ∈ pre ++ post, q.2 = H q.1)
    (state : State) (tail : Bytes) (htail : tail.length = 224)
    (hframe : 294 ≤ L) (hsize : 162 ≤ L) (hnode : 257 ≤ L)
    (packed salt : List AspisR1.ExactLeafFieldCodec.Byte)
    (hw : packed.length = 128) (hs : salt.length = 32)
    (leaf : Fin 65536)
    (path : Path (MerkleIndexGeometry.slots 6 leaf.val)) (root : State)
    (hcommit : Read pre
      (CommitmentRootFrames.foldedAddr state root tail htail hframe))
    (haccept : (eval H (CanonicalMerkleProgram.program path
      (leafInput 0x72 packed salt))).2 = root)
    (hopen : ∀ a, Read (eval H (CanonicalMerkleProgram.program path
      (leafInput 0x72 packed salt))).1 a → Read (pre ++ post) a)
    (hQ : firstReads emptyTable (pre ++ post) ≤ Qtot)
    (hnoColl : ¬ hitsBad (badColl p Qtot) emptyTable (pre ++ post))
    (hnoChild : ¬ hitsBad (ParsedTargetsCollision.bad MerkleChildTargets.pred Qtot)
      emptyTable (pre ++ post))
    (hnoRoot : ¬ hitsBad
      (ParsedTargetsCollision.bad CommitmentRootTargets.pred Qtot) emptyTable
      (pre ++ post))
    (payload : AspisR1.FoldedLeafCodec.Folded)
    (hdecode : decodeFolded packed = some payload)
    (i : Fin 262144) (hindex : foldedIndex i = leaf) :
    FoldedRecoveredWord.wordAt (pre ++ post) root i = payload (foldedSlot i) := by
  have hpacked : FoldedRecoveredWord.packedAt (pre ++ post) root leaf = some packed := by
    have hbefore : recoverAt 0x72 128 pre
        (MerkleIndexGeometry.slots 6 leaf.val) root = some (packed, salt) := by
      exact ThreeCommitmentFullTrace.folded_recover_of_no_events p Qtot H pre post hcons
        state tail htail hframe hsize hnode packed salt hw hs path root hcommit haccept
        hopen hQ hnoColl hnoChild hnoRoot
    have hfull := CanonicalRecoveryStability.later_of_earlier 0x72 128 pre post
      (MerkleIndexGeometry.slots 6 leaf.val) root (packed, salt) hbefore
    simp [FoldedRecoveredWord.packedAt, hfull]
  unfold FoldedRecoveredWord.wordAt
  rw [hindex]
  exact wordOfPacked_success _ packed payload i hpacked hdecode

#print axioms folded_word_of_no_events

end AspisR1.CanonicalTypedOpening
