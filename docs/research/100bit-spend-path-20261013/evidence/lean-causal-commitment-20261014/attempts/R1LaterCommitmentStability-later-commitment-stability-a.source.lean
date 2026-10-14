import R1CanonicalRecoveryStability
import R1FixedFrameNoMerkle
import R1CommitmentRootFrames

/-! C2 and folded-root recovery are unchanged when their literal fixed frame
is appended before an arbitrary continuation. -/
set_option autoImplicit false
namespace AspisR1.LaterCommitmentStability

open FS FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open Merkle32Path Merkle32Leaf MerkleTable MerkleLeafRecovery MerkleRecordedLog
open CanonicalByteHash

variable {M Cv : Type} {L : Nat}

theorem c2_recover_stable (p : Params M Cv L) (Qtot : Nat)
    (H : Addr L → State) (pre post : List (Addr L × State))
    (state : State) (hframe : 71 ≤ L) (root answer : State)
    (hsize : 162 ≤ L) (hnode : 257 ≤ L)
    (hcons : ∀ q ∈
      (pre ++ [(CommitmentRootFrames.c2Addr state root hframe, answer)]) ++ post,
      q.2 = H q.1)
    (hQ : firstReads emptyTable
      ((pre ++ [(CommitmentRootFrames.c2Addr state root hframe, answer)]) ++ post) ≤ Qtot)
    (hnoColl : ¬ hitsBad (badColl p Qtot) emptyTable
      ((pre ++ [(CommitmentRootFrames.c2Addr state root hframe, answer)]) ++ post))
    (hnoChild : ¬ hitsBad (ParsedTargetsCollision.bad MerkleChildTargets.pred Qtot)
      emptyTable ((pre ++ [(CommitmentRootFrames.c2Addr state root hframe, answer)]) ++ post))
    (hnoRoot : ¬ hitsBad (ParsedTargetsCollision.bad CommitmentRootTargets.pred Qtot)
      emptyTable ((pre ++ [(CommitmentRootFrames.c2Addr state root hframe, answer)]) ++ post))
    (slots : List (Fin 8)) :
    CanonicalRecoveryStability.recoverAt 0xf1 128 pre slots root =
      CanonicalRecoveryStability.recoverAt 0xf1 128
        ((pre ++ [(CommitmentRootFrames.c2Addr state root hframe, answer)]) ++ post)
        slots root := by
  let bs := CommitmentRootFrames.c2Frame state root
  have hfits : bs.length ≤ L := by
    have hh : bs.length = 71 := CommitmentRootFrames.c2Frame_length state root
    rw [hh]
    exact hframe
  have haddr : CommitmentRootFrames.c2Addr state root hframe = Addr.ofBytes bs hfits := by
    rfl
  let frameAddr := CommitmentRootFrames.c2Addr state root hframe
  let midpre := pre ++ [(frameAddr, answer)]
  have hcommit : Read midpre frameAddr := by
    change frameAddr ∈ midpre.map Prod.fst
    simp [midpre, frameAddr, List.map_append]
  have hstable := CanonicalRecoveryStability.recover_stable p Qtot H midpre post
    hcons 0xf1 128 hsize hnode slots root CommitmentRootTargets.pred frameAddr 0
    hcommit (CommitmentRootFrames.pred_c2 state root hframe) hQ
    hnoColl hnoChild hnoRoot
  have hfixed := FixedFrameNoMerkle.recover_unchanged_of_length_ne 0xf1 128 pre bs
    hfits answer slots root (by rw [CommitmentRootFrames.c2Frame_length]; omega)
    (by rw [CommitmentRootFrames.c2Frame_length]; omega)
  have hremove : CanonicalRecoveryStability.recoverAt 0xf1 128 midpre slots root =
      CanonicalRecoveryStability.recoverAt 0xf1 128 pre slots root := by
    unfold CanonicalRecoveryStability.recoverAt
    rw [haddr]
    exact hfixed
  calc
    CanonicalRecoveryStability.recoverAt 0xf1 128 pre slots root =
        CanonicalRecoveryStability.recoverAt 0xf1 128 midpre slots root := hremove.symm
    _ = CanonicalRecoveryStability.recoverAt 0xf1 128 (midpre ++ post) slots root := hstable
    _ = CanonicalRecoveryStability.recoverAt 0xf1 128
          ((pre ++ [(CommitmentRootFrames.c2Addr state root hframe, answer)]) ++ post)
          slots root := by rfl

theorem c2_word_stable (p : Params M Cv L) (Qtot : Nat)
    (H : Addr L → State) (pre post : List (Addr L × State))
    (state : State) (hframe : 71 ≤ L) (root answer : State)
    (hsize : 162 ≤ L) (hnode : 257 ≤ L)
    (hcons : ∀ q ∈
      (pre ++ [(CommitmentRootFrames.c2Addr state root hframe, answer)]) ++ post,
      q.2 = H q.1)
    (hQ : firstReads emptyTable
      ((pre ++ [(CommitmentRootFrames.c2Addr state root hframe, answer)]) ++ post) ≤ Qtot)
    (hnoColl : ¬ hitsBad (badColl p Qtot) emptyTable
      ((pre ++ [(CommitmentRootFrames.c2Addr state root hframe, answer)]) ++ post))
    (hnoChild : ¬ hitsBad (ParsedTargetsCollision.bad MerkleChildTargets.pred Qtot)
      emptyTable ((pre ++ [(CommitmentRootFrames.c2Addr state root hframe, answer)]) ++ post))
    (hnoRoot : ¬ hitsBad (ParsedTargetsCollision.bad CommitmentRootTargets.pred Qtot)
      emptyTable ((pre ++ [(CommitmentRootFrames.c2Addr state root hframe, answer)]) ++ post)) :
    (fun slots => CanonicalRecoveryStability.recoverAt 0xf1 128 pre slots root) =
      (fun slots => CanonicalRecoveryStability.recoverAt 0xf1 128
        ((pre ++ [(CommitmentRootFrames.c2Addr state root hframe, answer)]) ++ post)
        slots root) := by
  funext slots
  exact c2_recover_stable p Qtot H pre post state hframe root answer hsize hnode
    hcons hQ hnoColl hnoChild hnoRoot slots

theorem folded_recover_stable (p : Params M Cv L) (Qtot : Nat)
    (H : Addr L → State) (pre post : List (Addr L × State))
    (state : State) (tail : Bytes) (htail : tail.length = 224)
    (hframe : 294 ≤ L) (root answer : State)
    (hsize : 162 ≤ L) (hnode : 257 ≤ L)
    (hcons : ∀ q ∈
      (pre ++ [(CommitmentRootFrames.foldedAddr state root tail htail hframe, answer)]) ++ post,
      q.2 = H q.1)
    (hQ : firstReads emptyTable
      ((pre ++ [(CommitmentRootFrames.foldedAddr state root tail htail hframe, answer)]) ++ post) ≤ Qtot)
    (hnoColl : ¬ hitsBad (badColl p Qtot) emptyTable
      ((pre ++ [(CommitmentRootFrames.foldedAddr state root tail htail hframe, answer)]) ++ post))
    (hnoChild : ¬ hitsBad (ParsedTargetsCollision.bad MerkleChildTargets.pred Qtot)
      emptyTable ((pre ++ [(CommitmentRootFrames.foldedAddr state root tail htail hframe, answer)]) ++ post))
    (hnoRoot : ¬ hitsBad (ParsedTargetsCollision.bad CommitmentRootTargets.pred Qtot)
      emptyTable ((pre ++ [(CommitmentRootFrames.foldedAddr state root tail htail hframe, answer)]) ++ post))
    (slots : List (Fin 8)) :
    CanonicalRecoveryStability.recoverAt 0x72 128 pre slots root =
      CanonicalRecoveryStability.recoverAt 0x72 128
        ((pre ++ [(CommitmentRootFrames.foldedAddr state root tail htail hframe, answer)]) ++ post)
        slots root := by
  let bs := CommitmentRootFrames.foldedFrame state root tail
  have hfits : bs.length ≤ L := by
    have hh : bs.length = 294 := CommitmentRootFrames.foldedFrame_length state root tail htail
    rw [hh]
    exact hframe
  have haddr : CommitmentRootFrames.foldedAddr state root tail htail hframe =
      Addr.ofBytes bs hfits := by
    rfl
  let frameAddr := CommitmentRootFrames.foldedAddr state root tail htail hframe
  let midpre := pre ++ [(frameAddr, answer)]
  have hcommit : Read midpre frameAddr := by
    change frameAddr ∈ midpre.map Prod.fst
    simp [midpre, frameAddr, List.map_append]
  have hstable := CanonicalRecoveryStability.recover_stable p Qtot H midpre post
    hcons 0x72 128 hsize hnode slots root CommitmentRootTargets.pred frameAddr 1
    hcommit (CommitmentRootFrames.pred_folded state root tail htail hframe) hQ
    hnoColl hnoChild hnoRoot
  have hfixed := FixedFrameNoMerkle.recover_unchanged_of_length_ne 0x72 128 pre bs
    hfits answer slots root (by rw [CommitmentRootFrames.foldedFrame_length _ _ _ htail]; omega)
    (by rw [CommitmentRootFrames.foldedFrame_length _ _ _ htail]; omega)
  have hremove : CanonicalRecoveryStability.recoverAt 0x72 128 midpre slots root =
      CanonicalRecoveryStability.recoverAt 0x72 128 pre slots root := by
    unfold CanonicalRecoveryStability.recoverAt
    rw [haddr]
    exact hfixed
  calc
    CanonicalRecoveryStability.recoverAt 0x72 128 pre slots root =
        CanonicalRecoveryStability.recoverAt 0x72 128 midpre slots root := hremove.symm
    _ = CanonicalRecoveryStability.recoverAt 0x72 128 (midpre ++ post) slots root := hstable
    _ = CanonicalRecoveryStability.recoverAt 0x72 128
          ((pre ++ [(CommitmentRootFrames.foldedAddr state root tail htail hframe, answer)]) ++ post)
          slots root := by rfl

theorem folded_word_stable (p : Params M Cv L) (Qtot : Nat)
    (H : Addr L → State) (pre post : List (Addr L × State))
    (state : State) (tail : Bytes) (htail : tail.length = 224)
    (hframe : 294 ≤ L) (root answer : State)
    (hsize : 162 ≤ L) (hnode : 257 ≤ L)
    (hcons : ∀ q ∈
      (pre ++ [(CommitmentRootFrames.foldedAddr state root tail htail hframe, answer)]) ++ post,
      q.2 = H q.1)
    (hQ : firstReads emptyTable
      ((pre ++ [(CommitmentRootFrames.foldedAddr state root tail htail hframe, answer)]) ++ post) ≤ Qtot)
    (hnoColl : ¬ hitsBad (badColl p Qtot) emptyTable
      ((pre ++ [(CommitmentRootFrames.foldedAddr state root tail htail hframe, answer)]) ++ post))
    (hnoChild : ¬ hitsBad (ParsedTargetsCollision.bad MerkleChildTargets.pred Qtot)
      emptyTable ((pre ++ [(CommitmentRootFrames.foldedAddr state root tail htail hframe, answer)]) ++ post))
    (hnoRoot : ¬ hitsBad (ParsedTargetsCollision.bad CommitmentRootTargets.pred Qtot)
      emptyTable ((pre ++ [(CommitmentRootFrames.foldedAddr state root tail htail hframe, answer)]) ++ post)) :
    (fun slots => CanonicalRecoveryStability.recoverAt 0x72 128 pre slots root) =
      (fun slots => CanonicalRecoveryStability.recoverAt 0x72 128
        ((pre ++ [(CommitmentRootFrames.foldedAddr state root tail htail hframe, answer)]) ++ post)
        slots root) := by
  funext slots
  exact folded_recover_stable p Qtot H pre post state tail htail hframe root answer
    hsize hnode hcons hQ hnoColl hnoChild hnoRoot slots

#print axioms c2_recover_stable
#print axioms c2_word_stable
#print axioms folded_recover_stable
#print axioms folded_word_stable

end AspisR1.LaterCommitmentStability
