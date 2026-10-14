import R1CanonicalBoundRecovery
import R1CommitmentRootFrames

/-! Literal C1, C2, and folded-root specializations of canonical finite-table
recovery. Each retains the stated frame read, Merkle path acceptance, query
bound, and the three corresponding bad-event exclusions. -/
set_option autoImplicit false
namespace AspisR1.ThreeCommitmentRecovery

open FS FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open Merkle32Path Merkle32Leaf MerkleTable MerkleLeafRecovery MerkleRecordedLog
open CanonicalByteHash

variable {M Cv : Type} {L : Nat}

theorem c1_recover_of_no_events (p : Params M Cv L) (Qtot : Nat)
    (H : Addr L → State) (pre : List (Addr L × State))
    (hpre : ∀ q ∈ pre, q.2 = H q.1)
    (pubBytes : Bytes) (hframe : 75 + pubBytes.length ≤ L)
    (hsize : 514 ≤ L) (hnode : 257 ≤ L)
    (packed salt : Bytes) (hw : packed.length = 480) (hs : salt.length = 32)
    {slots : List (Fin 8)} (path : Path slots) (root : State)
    (hcommit : Read pre (PublicInitFrame.addr pubBytes hframe root))
    (haccept : (eval H (CanonicalMerkleProgram.program path
      (leafInput 0x71 packed salt))).2 = root)
    (hQ : firstReads emptyTable (pre ++ (eval H (CanonicalMerkleProgram.program path
      (leafInput 0x71 packed salt))).1) ≤ Qtot)
    (hnoColl : ¬ hitsBad (badColl p Qtot) emptyTable
      (pre ++ (eval H (CanonicalMerkleProgram.program path
        (leafInput 0x71 packed salt))).1))
    (hnoChild : ¬ hitsBad (ParsedTargetsCollision.bad MerkleChildTargets.pred Qtot)
      emptyTable (pre ++ (eval H (CanonicalMerkleProgram.program path
        (leafInput 0x71 packed salt))).1))
    (hnoRoot : ¬ hitsBad
      (ParsedTargetsCollision.bad CommitmentRootTargets.pred Qtot) emptyTable
      (pre ++ (eval H (CanonicalMerkleProgram.program path
        (leafInput 0x71 packed salt))).1)) :
    recover (nodes (CanonicalOracleLog.byteLog pre))
        (leaves 0x71 480 (CanonicalOracleLog.byteLog pre)) slots root =
        some (packed, salt) := by
  have hleaf : (leafInput 0x71 packed salt).length ≤ L := by
    rw [Merkle32Leaf.leaf_input_length 0x71 packed salt hs, hw]
    exact hsize
  exact CanonicalBoundRecovery.recover_of_no_events p Qtot H pre hpre
    0x71 480 packed salt hw hs hleaf hnode path root CommitmentRootTargets.pred
    (PublicInitFrame.addr pubBytes hframe root) 0 hcommit
    (CommitmentRootFrames.pred_c1 pubBytes hframe root) haccept hQ hnoColl hnoChild hnoRoot

theorem c2_recover_of_no_events (p : Params M Cv L) (Qtot : Nat)
    (H : Addr L → State) (pre : List (Addr L × State))
    (hpre : ∀ q ∈ pre, q.2 = H q.1)
    (state : State) (hframe : 71 ≤ L)
    (hsize : 162 ≤ L) (hnode : 257 ≤ L)
    (packed salt : Bytes) (hw : packed.length = 128) (hs : salt.length = 32)
    {slots : List (Fin 8)} (path : Path slots) (root : State)
    (hcommit : Read pre (CommitmentRootFrames.c2Addr state root hframe))
    (haccept : (eval H (CanonicalMerkleProgram.program path
      (leafInput 0xf1 packed salt))).2 = root)
    (hQ : firstReads emptyTable (pre ++ (eval H (CanonicalMerkleProgram.program path
      (leafInput 0xf1 packed salt))).1) ≤ Qtot)
    (hnoColl : ¬ hitsBad (badColl p Qtot) emptyTable
      (pre ++ (eval H (CanonicalMerkleProgram.program path
        (leafInput 0xf1 packed salt))).1))
    (hnoChild : ¬ hitsBad (ParsedTargetsCollision.bad MerkleChildTargets.pred Qtot)
      emptyTable (pre ++ (eval H (CanonicalMerkleProgram.program path
        (leafInput 0xf1 packed salt))).1))
    (hnoRoot : ¬ hitsBad
      (ParsedTargetsCollision.bad CommitmentRootTargets.pred Qtot) emptyTable
      (pre ++ (eval H (CanonicalMerkleProgram.program path
        (leafInput 0xf1 packed salt))).1)) :
    recover (nodes (CanonicalOracleLog.byteLog pre))
        (leaves 0xf1 128 (CanonicalOracleLog.byteLog pre)) slots root =
        some (packed, salt) := by
  have hleaf : (leafInput 0xf1 packed salt).length ≤ L := by
    rw [Merkle32Leaf.leaf_input_length 0xf1 packed salt hs, hw]
    exact hsize
  exact CanonicalBoundRecovery.recover_of_no_events p Qtot H pre hpre
    0xf1 128 packed salt hw hs hleaf hnode path root CommitmentRootTargets.pred
    (CommitmentRootFrames.c2Addr state root hframe) 0 hcommit
    (CommitmentRootFrames.pred_c2 state root hframe) haccept hQ hnoColl hnoChild hnoRoot

theorem folded_recover_of_no_events (p : Params M Cv L) (Qtot : Nat)
    (H : Addr L → State) (pre : List (Addr L × State))
    (hpre : ∀ q ∈ pre, q.2 = H q.1)
    (state : State) (tail : Bytes) (htail : tail.length = 224)
    (hframe : 294 ≤ L) (hsize : 162 ≤ L) (hnode : 257 ≤ L)
    (packed salt : Bytes) (hw : packed.length = 128) (hs : salt.length = 32)
    {slots : List (Fin 8)} (path : Path slots) (root : State)
    (hcommit : Read pre
      (CommitmentRootFrames.foldedAddr state root tail htail hframe))
    (haccept : (eval H (CanonicalMerkleProgram.program path
      (leafInput 0x72 packed salt))).2 = root)
    (hQ : firstReads emptyTable (pre ++ (eval H (CanonicalMerkleProgram.program path
      (leafInput 0x72 packed salt))).1) ≤ Qtot)
    (hnoColl : ¬ hitsBad (badColl p Qtot) emptyTable
      (pre ++ (eval H (CanonicalMerkleProgram.program path
        (leafInput 0x72 packed salt))).1))
    (hnoChild : ¬ hitsBad (ParsedTargetsCollision.bad MerkleChildTargets.pred Qtot)
      emptyTable (pre ++ (eval H (CanonicalMerkleProgram.program path
        (leafInput 0x72 packed salt))).1))
    (hnoRoot : ¬ hitsBad
      (ParsedTargetsCollision.bad CommitmentRootTargets.pred Qtot) emptyTable
      (pre ++ (eval H (CanonicalMerkleProgram.program path
        (leafInput 0x72 packed salt))).1)) :
    recover (nodes (CanonicalOracleLog.byteLog pre))
        (leaves 0x72 128 (CanonicalOracleLog.byteLog pre)) slots root =
        some (packed, salt) := by
  have hleaf : (leafInput 0x72 packed salt).length ≤ L := by
    rw [Merkle32Leaf.leaf_input_length 0x72 packed salt hs, hw]
    exact hsize
  exact CanonicalBoundRecovery.recover_of_no_events p Qtot H pre hpre
    0x72 128 packed salt hw hs hleaf hnode path root CommitmentRootTargets.pred
    (CommitmentRootFrames.foldedAddr state root tail htail hframe) 1 hcommit
    (CommitmentRootFrames.pred_folded state root tail htail hframe)
    haccept hQ hnoColl hnoChild hnoRoot

#print axioms c1_recover_of_no_events
#print axioms c2_recover_of_no_events
#print axioms folded_recover_of_no_events

end AspisR1.ThreeCommitmentRecovery
