import R1CanonicalFullTraceRecovery
import R1CommitmentRootFrames

/-! C1, C2, and folded-root specializations of recovery over an arbitrary
consistent actual trace containing the prior and opening-program reads. -/
set_option autoImplicit false
namespace AspisR1.ThreeCommitmentFullTrace

open FS FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open Merkle32Path Merkle32Leaf MerkleTable MerkleLeafRecovery MerkleRecordedLog
open CanonicalByteHash

variable {M Cv : Type} {L : Nat}

theorem c1_recover_of_no_events (p : Params M Cv L) (Qtot : Nat)
    (H : Addr L → State) (pre post : List (Addr L × State))
    (hcons : ∀ q ∈ pre ++ post, q.2 = H q.1)
    (pubBytes : Bytes) (hframe : 75 + pubBytes.length ≤ L)
    (hsize : 514 ≤ L) (hnode : 257 ≤ L)
    (packed salt : Bytes) (hw : packed.length = 480) (hs : salt.length = 32)
    {slots : List (Fin 8)} (path : Path slots) (root : State)
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
      (pre ++ post)) :
    recover (nodes (CanonicalOracleLog.byteLog pre))
        (leaves 0x71 480 (CanonicalOracleLog.byteLog pre)) slots root =
        some (packed, salt) := by
  have hleaf : (leafInput 0x71 packed salt).length ≤ L := by
    rw [Merkle32Leaf.leaf_input_length 0x71 packed salt hs, hw]
    exact hsize
  exact CanonicalFullTraceRecovery.recover_of_no_events p Qtot H pre post hcons
    0x71 480 packed salt hw hs hleaf hnode path root CommitmentRootTargets.pred
    (PublicInitFrame.addr pubBytes hframe root) 0 hcommit
    (CommitmentRootFrames.pred_c1 pubBytes hframe root) haccept hopen hQ
    hnoColl hnoChild hnoRoot

theorem c2_recover_of_no_events (p : Params M Cv L) (Qtot : Nat)
    (H : Addr L → State) (pre post : List (Addr L × State))
    (hcons : ∀ q ∈ pre ++ post, q.2 = H q.1)
    (state : State) (hframe : 71 ≤ L) (hsize : 162 ≤ L) (hnode : 257 ≤ L)
    (packed salt : Bytes) (hw : packed.length = 128) (hs : salt.length = 32)
    {slots : List (Fin 8)} (path : Path slots) (root : State)
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
      (pre ++ post)) :
    recover (nodes (CanonicalOracleLog.byteLog pre))
        (leaves 0xf1 128 (CanonicalOracleLog.byteLog pre)) slots root =
        some (packed, salt) := by
  have hleaf : (leafInput 0xf1 packed salt).length ≤ L := by
    rw [Merkle32Leaf.leaf_input_length 0xf1 packed salt hs, hw]
    exact hsize
  exact CanonicalFullTraceRecovery.recover_of_no_events p Qtot H pre post hcons
    0xf1 128 packed salt hw hs hleaf hnode path root CommitmentRootTargets.pred
    (CommitmentRootFrames.c2Addr state root hframe) 0 hcommit
    (CommitmentRootFrames.pred_c2 state root hframe) haccept hopen hQ
    hnoColl hnoChild hnoRoot

theorem folded_recover_of_no_events (p : Params M Cv L) (Qtot : Nat)
    (H : Addr L → State) (pre post : List (Addr L × State))
    (hcons : ∀ q ∈ pre ++ post, q.2 = H q.1)
    (state : State) (tail : Bytes) (htail : tail.length = 224)
    (hframe : 294 ≤ L) (hsize : 162 ≤ L) (hnode : 257 ≤ L)
    (packed salt : Bytes) (hw : packed.length = 128) (hs : salt.length = 32)
    {slots : List (Fin 8)} (path : Path slots) (root : State)
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
      (pre ++ post)) :
    recover (nodes (CanonicalOracleLog.byteLog pre))
        (leaves 0x72 128 (CanonicalOracleLog.byteLog pre)) slots root =
        some (packed, salt) := by
  have hleaf : (leafInput 0x72 packed salt).length ≤ L := by
    rw [Merkle32Leaf.leaf_input_length 0x72 packed salt hs, hw]
    exact hsize
  exact CanonicalFullTraceRecovery.recover_of_no_events p Qtot H pre post hcons
    0x72 128 packed salt hw hs hleaf hnode path root CommitmentRootTargets.pred
    (CommitmentRootFrames.foldedAddr state root tail htail hframe) 1 hcommit
    (CommitmentRootFrames.pred_folded state root tail htail hframe) haccept hopen hQ
    hnoColl hnoChild hnoRoot

#print axioms c1_recover_of_no_events
#print axioms c2_recover_of_no_events
#print axioms folded_recover_of_no_events

end AspisR1.ThreeCommitmentFullTrace
