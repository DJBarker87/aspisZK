import R1CanonicalRecoveryStability
import R1InitialFrameNoMerkle
import R1CommitmentRootFrames

/-! C1 finite-table recovery is unchanged by appending the literal public
initialization frame before the arbitrary continuation. -/
set_option autoImplicit false
namespace AspisR1.C1BeforeFrameStability

open FS FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open Merkle32Path Merkle32Leaf MerkleTable MerkleLeafRecovery MerkleRecordedLog
open CanonicalByteHash

variable {M Cv : Type} {L : Nat}

theorem c1_recover_stable (p : Params M Cv L) (Qtot : Nat)
    (H : Addr L → State) (pre post : List (Addr L × State))
    (pubBytes : Bytes) (hframe : 75 + pubBytes.length ≤ L)
    (root answer : State) (hsize : 514 ≤ L) (hnode : 257 ≤ L)
    (hcons : ∀ q ∈
      (pre ++ [(PublicInitFrame.addr pubBytes hframe root, answer)]) ++ post,
      q.2 = H q.1)
    (hQ : firstReads emptyTable
      ((pre ++ [(PublicInitFrame.addr pubBytes hframe root, answer)]) ++ post) ≤ Qtot)
    (hnoColl : ¬ hitsBad (badColl p Qtot) emptyTable
      ((pre ++ [(PublicInitFrame.addr pubBytes hframe root, answer)]) ++ post))
    (hnoChild : ¬ hitsBad (ParsedTargetsCollision.bad MerkleChildTargets.pred Qtot)
      emptyTable ((pre ++ [(PublicInitFrame.addr pubBytes hframe root, answer)]) ++ post))
    (hnoRoot : ¬ hitsBad (ParsedTargetsCollision.bad CommitmentRootTargets.pred Qtot)
      emptyTable ((pre ++ [(PublicInitFrame.addr pubBytes hframe root, answer)]) ++ post))
    (slots : List (Fin 8)) :
    CanonicalRecoveryStability.recoverAt 0x71 480 pre slots root =
      CanonicalRecoveryStability.recoverAt 0x71 480
        ((pre ++ [(PublicInitFrame.addr pubBytes hframe root, answer)]) ++ post)
        slots root := by
  let frame := PublicInitFrame.addr pubBytes hframe root
  let midpre := pre ++ [(frame, answer)]
  have hcommit : Read midpre frame := by
    change frame ∈ midpre.map Prod.fst
    simp [midpre, frame, List.map_append]
  have hstable := CanonicalRecoveryStability.recover_stable p Qtot H midpre post
    hcons 0x71 480 hsize hnode slots root CommitmentRootTargets.pred frame 0
    hcommit (CommitmentRootFrames.pred_c1 pubBytes hframe root) hQ
    hnoColl hnoChild hnoRoot
  have hremove := InitialFrameNoMerkle.recover_unchanged 0x71 480 pre pubBytes
    hframe root answer slots root
  change CanonicalRecoveryStability.recoverAt 0x71 480 midpre slots root =
    CanonicalRecoveryStability.recoverAt 0x71 480 pre slots root at hremove
  calc
    CanonicalRecoveryStability.recoverAt 0x71 480 pre slots root =
        CanonicalRecoveryStability.recoverAt 0x71 480 midpre slots root := hremove.symm
    _ = CanonicalRecoveryStability.recoverAt 0x71 480 (midpre ++ post) slots root := hstable
    _ = CanonicalRecoveryStability.recoverAt 0x71 480
          ((pre ++ [(PublicInitFrame.addr pubBytes hframe root, answer)]) ++ post)
          slots root := by rfl

theorem c1_word_stable (p : Params M Cv L) (Qtot : Nat)
    (H : Addr L → State) (pre post : List (Addr L × State))
    (pubBytes : Bytes) (hframe : 75 + pubBytes.length ≤ L)
    (root answer : State) (hsize : 514 ≤ L) (hnode : 257 ≤ L)
    (hcons : ∀ q ∈
      (pre ++ [(PublicInitFrame.addr pubBytes hframe root, answer)]) ++ post,
      q.2 = H q.1)
    (hQ : firstReads emptyTable
      ((pre ++ [(PublicInitFrame.addr pubBytes hframe root, answer)]) ++ post) ≤ Qtot)
    (hnoColl : ¬ hitsBad (badColl p Qtot) emptyTable
      ((pre ++ [(PublicInitFrame.addr pubBytes hframe root, answer)]) ++ post))
    (hnoChild : ¬ hitsBad (ParsedTargetsCollision.bad MerkleChildTargets.pred Qtot)
      emptyTable ((pre ++ [(PublicInitFrame.addr pubBytes hframe root, answer)]) ++ post))
    (hnoRoot : ¬ hitsBad (ParsedTargetsCollision.bad CommitmentRootTargets.pred Qtot)
      emptyTable ((pre ++ [(PublicInitFrame.addr pubBytes hframe root, answer)]) ++ post)) :
    (fun slots => CanonicalRecoveryStability.recoverAt 0x71 480 pre slots root) =
      (fun slots => CanonicalRecoveryStability.recoverAt 0x71 480
        ((pre ++ [(PublicInitFrame.addr pubBytes hframe root, answer)]) ++ post)
        slots root) := by
  funext slots
  exact c1_recover_stable p Qtot H pre post pubBytes hframe root answer hsize hnode
    hcons hQ hnoColl hnoChild hnoRoot slots

#print axioms c1_recover_stable
#print axioms c1_word_stable

end AspisR1.C1BeforeFrameStability
