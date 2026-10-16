import R1CanonicalTypedOpening
import R1TypedRecoveryStability
import R1LaterTableStability
import R1MerkleIndexGeometry
import R1CommitmentRootFrames
import R1MixedLeafDecoder

/-! Move accepted strict Merkle openings back to the typed packed map at the
first-read commitment cut. Each theorem keeps the concrete read, table,
consistency, length and bad-event premises of the established recovery paths.
-/
set_option autoImplicit false

namespace AspisR1.CanonicalCutOpening

open FS FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open AspisV8PairedCommitment
open AspisR1.CanonicalTypedOpening
open AspisR1.TypedRecoveryStability
open AspisR1.FoldedRecoveredWord
open AspisR1.MerkleIndexGeometry
open AspisR1.MixedLeafDecoder
open AspisR1.ExactLeafFieldCodec
open AspisR1.CanonicalFullTraceRecovery
open AspisR1.CanonicalByteHash
open AspisR1.MixedLeafEncoding
open Merkle32Path Merkle32Leaf MerkleTable MerkleLeafRecovery MerkleRecordedLog

variable {M Cv : Type} {L : Nat}

private def paths6Folded : Fin 65536 → List (Fin 8) :=
  fun leaf => MerkleIndexGeometry.slots 6 leaf.val

theorem c1_cut_decode_matches_opening
    (p : Params M Cv L) (Qtot : Nat)
    (H : Addr L → State) (tr represented : List (Addr L × State))
    (hcons : ∀ q ∈ tr, q.2 = H q.1)
    (hrepresented : ∀ q ∈ represented, q.2 = H q.1)
    (pubBytes : Bytes) (hframe : 75 + pubBytes.length ≤ L)
    (initRoot : State) (hsize : 514 ≤ L) (hnode : 257 ≤ L)
    (hcutRead : Read tr (PublicInitFrame.addr pubBytes hframe initRoot))
    (hcutTable : TraceTable.replay (emptyTable : Table (Addr L) State) represented =
      tableBefore emptyTable tr (PublicInitFrame.addr pubBytes hframe initRoot))
    (packed salt : List AspisR1.ExactLeafFieldCodec.Byte) (hw : packed.length = 480) (hs : salt.length = 32)
    (leaf : Fin 262144)
    (path : Path (MerkleIndexGeometry.slots 6 leaf.val))
    (haccept : (eval H (CanonicalMerkleProgram.program path
      (AspisR1.Merkle32Leaf.leafInput 0x71 packed salt))).2 = initRoot)
    (hopen : ∀ a, Read (eval H (CanonicalMerkleProgram.program path
      (AspisR1.Merkle32Leaf.leafInput 0x71 packed salt))).1 a → Read (tr) a)
    (hQ : firstReads emptyTable tr ≤ Qtot)
    (hnoColl : ¬ hitsBad (badColl p Qtot) emptyTable tr)
    (hnoChild : ¬ hitsBad
      (ParsedTargetsCollision.bad MerkleChildTargets.pred Qtot) emptyTable tr)
    (hnoRoot : ¬ hitsBad
      (ParsedTargetsCollision.bad CommitmentRootTargets.pred Qtot) emptyTable tr)
    (payload : AspisR1.TypedRecoveredWords.C1) (hdecode : decodeC1 packed = some payload) :
    AspisR1.TypedRecoveredWords.decodeC1At (c1PackedAt represented AspisR1.CanonicalTypedOpening.paths6C1C2 initRoot) leaf = some payload := by
  have hstable := c1_packed_stable p Qtot H tr represented pubBytes hframe initRoot
    hsize hnode hcons hQ hnoColl hnoChild hnoRoot hrepresented hcutRead hcutTable
    AspisR1.CanonicalTypedOpening.paths6C1C2
  rw [hstable]
  have hcons' : ∀ q ∈ tr ++ [], q.2 = H q.1 := by simpa using hcons
  simpa [List.append_nil, AspisR1.CanonicalTypedOpening.paths6C1C2] using
    (c1_decode_of_no_events p Qtot H tr [] hcons' pubBytes hframe hsize hnode
      packed salt hw hs leaf path initRoot hcutRead haccept
      (by simpa using hopen) (by simpa using hQ) (by simpa using hnoColl) (by simpa using hnoChild)
      (by simpa using hnoRoot) payload hdecode)

#print axioms c1_cut_decode_matches_opening

theorem c2_cut_decode_matches_opening
    (p : Params M Cv L) (Qtot : Nat)
    (H : Addr L → State) (tr represented : List (Addr L × State))
    (hcons : ∀ q ∈ tr, q.2 = H q.1)
    (hrepresented : ∀ q ∈ represented, q.2 = H q.1)
    (state : State) (hframe : 71 ≤ L) (c2Root : State)
    (hsize : 162 ≤ L) (hnode : 257 ≤ L)
    (hcutRead : Read tr (CommitmentRootFrames.c2Addr state c2Root hframe))
    (hcutTable : TraceTable.replay (emptyTable : Table (Addr L) State) represented =
      tableBefore emptyTable tr (CommitmentRootFrames.c2Addr state c2Root hframe))
    (packed salt : List AspisR1.ExactLeafFieldCodec.Byte) (hw : packed.length = 128) (hs : salt.length = 32)
    (leaf : Fin 262144)
    (path : Path (MerkleIndexGeometry.slots 6 leaf.val))
    (haccept : (eval H (CanonicalMerkleProgram.program path
      (AspisR1.Merkle32Leaf.leafInput 0xf1 packed salt))).2 = c2Root)
    (hopen : ∀ a, Read (eval H (CanonicalMerkleProgram.program path
      (AspisR1.Merkle32Leaf.leafInput 0xf1 packed salt))).1 a → Read tr a)
    (hQ : firstReads emptyTable tr ≤ Qtot)
    (hnoColl : ¬ hitsBad (badColl p Qtot) emptyTable tr)
    (hnoChild : ¬ hitsBad
      (ParsedTargetsCollision.bad MerkleChildTargets.pred Qtot) emptyTable tr)
    (hnoRoot : ¬ hitsBad
      (ParsedTargetsCollision.bad CommitmentRootTargets.pred Qtot) emptyTable tr)
    (payload : AspisR1.TypedRecoveredWords.C2) (hdecode : decodeC2 packed = some payload) :
    AspisR1.TypedRecoveredWords.decodeC2At (c2PackedAt represented AspisR1.CanonicalTypedOpening.paths6C1C2 c2Root) leaf = some payload := by
  have hstable := c2_packed_stable p Qtot H tr represented state hframe c2Root
    hsize hnode hcons hrepresented hcutRead hQ hnoColl hnoChild hnoRoot hcutTable
    AspisR1.CanonicalTypedOpening.paths6C1C2
  rw [hstable]
  have hcons' : ∀ q ∈ tr ++ [], q.2 = H q.1 := by simpa using hcons
  simpa [List.append_nil, AspisR1.CanonicalTypedOpening.paths6C1C2] using
    (c2_decode_of_no_events p Qtot H tr [] hcons' state hframe hsize hnode
      packed salt hw hs leaf path c2Root hcutRead haccept
      (by simpa using hopen) (by simpa using hQ) (by simpa using hnoColl) (by simpa using hnoChild)
      (by simpa using hnoRoot) payload hdecode)

#print axioms c2_cut_decode_matches_opening

theorem folded_cut_decode_matches_opening
    (p : Params M Cv L) (Qtot : Nat)
    (H : Addr L → State) (tr represented : List (Addr L × State))
    (hcons : ∀ q ∈ tr, q.2 = H q.1)
    (hrepresented : ∀ q ∈ represented, q.2 = H q.1)
    (state : State) (tail : Bytes) (htail : tail.length = 224)
    (hframe : 294 ≤ L) (foldedRoot : State)
    (hsize : 162 ≤ L) (hnode : 257 ≤ L)
    (hcutRead : Read tr (CommitmentRootFrames.foldedAddr state foldedRoot tail htail hframe))
    (hcutTable : TraceTable.replay (emptyTable : Table (Addr L) State) represented =
      tableBefore emptyTable tr
        (CommitmentRootFrames.foldedAddr state foldedRoot tail htail hframe))
    (packed salt : List AspisR1.ExactLeafFieldCodec.Byte) (hw : packed.length = 128) (hs : salt.length = 32)
    (leaf : Fin 65536)
    (path : Path (MerkleIndexGeometry.slots 6 leaf.val))
    (haccept : (eval H (CanonicalMerkleProgram.program path
      (AspisR1.Merkle32Leaf.leafInput 0x72 packed salt))).2 = foldedRoot)
    (hopen : ∀ a, Read (eval H (CanonicalMerkleProgram.program path
      (AspisR1.Merkle32Leaf.leafInput 0x72 packed salt))).1 a → Read tr a)
    (hQ : firstReads emptyTable tr ≤ Qtot)
    (hnoColl : ¬ hitsBad (badColl p Qtot) emptyTable tr)
    (hnoChild : ¬ hitsBad
      (ParsedTargetsCollision.bad MerkleChildTargets.pred Qtot) emptyTable tr)
    (hnoRoot : ¬ hitsBad
      (ParsedTargetsCollision.bad CommitmentRootTargets.pred Qtot) emptyTable tr)
    (payload : AspisR1.FoldedLeafCodec.Folded) (hdecode : AspisR1.FoldedLeafCodec.decodeFolded packed = some payload) :
    (FoldedRecoveredWord.packedAt represented foldedRoot leaf).bind AspisR1.FoldedLeafCodec.decodeFolded =
      some payload := by
  have hstable := AspisR1.LaterTableStability.folded_table_word_of_read p Qtot H tr represented
    state tail htail hframe foldedRoot hsize hnode hcons hrepresented hcutRead hQ
    hnoColl hnoChild hnoRoot hcutTable
  have hpackedStable :
      FoldedRecoveredWord.packedAt represented foldedRoot leaf =
        FoldedRecoveredWord.packedAt tr foldedRoot leaf := by
    unfold FoldedRecoveredWord.packedAt
    exact congrArg (fun f : List (Fin 8) → Option (List AspisR1.ExactLeafFieldCodec.Byte × List AspisR1.ExactLeafFieldCodec.Byte) =>
      (f (MerkleIndexGeometry.slots 6 leaf.val)).map Prod.fst) hstable
  rw [hpackedStable]
  have hcons' : ∀ q ∈ tr ++ [], q.2 = H q.1 := by simpa using hcons
  simpa [List.append_nil] using
    (folded_decode_of_no_events p Qtot H tr [] hcons' state tail htail hframe
      hsize hnode packed salt hw hs leaf path foldedRoot hcutRead haccept
      (by simpa using hopen) (by simpa using hQ) (by simpa using hnoColl) (by simpa using hnoChild)
      (by simpa using hnoRoot) payload hdecode)

#print axioms folded_cut_decode_matches_opening

end AspisR1.CanonicalCutOpening
