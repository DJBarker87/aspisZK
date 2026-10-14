import R1CanonicalTableRecovery
import R1LaterCommitmentStability
import R1FirstReadCut

/-! Transfer the fixed C2 and folded-root recovery functions from the
functional table at a read to a consistent full trace containing that read. -/
set_option autoImplicit false
namespace AspisR1.LaterTableStability

open FS FS2.Duplex
open AspisV8R19.SourceDuplexStep AspisV8R19.DuplexFrames
open AspisV8R19.MemoizedProgramLaw
open AspisV8PairedCommitment
open CanonicalByteHash CanonicalRecoveryStability

variable {M Cv : Type} {L : Nat}

theorem c2_table_word_of_read (p : Params M Cv L) (Qtot : Nat)
    (H : Addr L → State) (tr represented : List (Addr L × State))
    (state : State) (hframe : 71 ≤ L) (root : State)
    (hsize : 162 ≤ L) (hnode : 257 ≤ L)
    (hcons : ∀ q ∈ tr, q.2 = H q.1)
    (hrepresented : ∀ q ∈ represented, q.2 = H q.1)
    (hread : Read tr (CommitmentRootFrames.c2Addr state root hframe))
    (hQ : firstReads emptyTable tr ≤ Qtot)
    (hnoColl : ¬ hitsBad (badColl p Qtot) emptyTable tr)
    (hnoChild : ¬ hitsBad (ParsedTargetsCollision.bad MerkleChildTargets.pred Qtot)
      emptyTable tr)
    (hnoRoot : ¬ hitsBad (ParsedTargetsCollision.bad CommitmentRootTargets.pred Qtot)
      emptyTable tr)
    (htable : TraceTable.replay (emptyTable : Table (Addr L) State) represented =
      tableBefore emptyTable tr (CommitmentRootFrames.c2Addr state root hframe)) :
    (fun slots => recoverAt 0xf1 128 represented slots root) =
      (fun slots => recoverAt 0xf1 128 tr slots root) := by
  obtain ⟨pre, value, post, htr, hfirst⟩ :=
    FirstReadCut.first_read_cut tr (CommitmentRootFrames.c2Addr state root hframe) hread
  subst tr
  have hreshape :
      ((pre ++ [(CommitmentRootFrames.c2Addr state root hframe, value)]) ++ post) =
        pre ++ (CommitmentRootFrames.c2Addr state root hframe, value) :: post := by
    simp [List.append_assoc]
  have hcons' : ∀ q ∈ ((pre ++ [(CommitmentRootFrames.c2Addr state root hframe, value)]) ++ post),
      q.2 = H q.1 := by
    simpa only [hreshape] using hcons
  have hQ' : firstReads emptyTable
      ((pre ++ [(CommitmentRootFrames.c2Addr state root hframe, value)]) ++ post) ≤ Qtot := by
    simpa only [hreshape] using hQ
  have hnoColl' : ¬ hitsBad (badColl p Qtot) emptyTable
      ((pre ++ [(CommitmentRootFrames.c2Addr state root hframe, value)]) ++ post) := by
    simpa only [hreshape] using hnoColl
  have hnoChild' : ¬ hitsBad (ParsedTargetsCollision.bad MerkleChildTargets.pred Qtot)
      emptyTable ((pre ++ [(CommitmentRootFrames.c2Addr state root hframe, value)]) ++ post) := by
    simpa only [hreshape] using hnoChild
  have hnoRoot' : ¬ hitsBad (ParsedTargetsCollision.bad CommitmentRootTargets.pred Qtot)
      emptyTable ((pre ++ [(CommitmentRootFrames.c2Addr state root hframe, value)]) ++ post) := by
    simpa only [hreshape] using hnoRoot
  have hfullStable := LaterCommitmentStability.c2_word_stable p Qtot H pre post
    state hframe root value hsize hnode hcons' hQ' hnoColl' hnoChild' hnoRoot'
  funext slots
  have hrepresentedStable := CanonicalTableRecovery.represented_before_cut p Qtot H
    pre post represented (CommitmentRootFrames.c2Addr state root hframe) value hfirst
    hcons hrepresented hQ hnoColl htable 0xf1 128 slots root
  have hfullAt : recoverAt 0xf1 128 pre slots root =
      recoverAt 0xf1 128
        (pre ++ (CommitmentRootFrames.c2Addr state root hframe, value) :: post) slots root := by
    simpa only [hreshape] using congrFun hfullStable slots
  exact hrepresentedStable.symm.trans hfullAt

theorem folded_table_word_of_read (p : Params M Cv L) (Qtot : Nat)
    (H : Addr L → State) (tr represented : List (Addr L × State))
    (state : State) (tail : Bytes) (htail : tail.length = 224)
    (hframe : 294 ≤ L) (root : State)
    (hsize : 162 ≤ L) (hnode : 257 ≤ L)
    (hcons : ∀ q ∈ tr, q.2 = H q.1)
    (hrepresented : ∀ q ∈ represented, q.2 = H q.1)
    (hread : Read tr (CommitmentRootFrames.foldedAddr state root tail htail hframe))
    (hQ : firstReads emptyTable tr ≤ Qtot)
    (hnoColl : ¬ hitsBad (badColl p Qtot) emptyTable tr)
    (hnoChild : ¬ hitsBad (ParsedTargetsCollision.bad MerkleChildTargets.pred Qtot)
      emptyTable tr)
    (hnoRoot : ¬ hitsBad (ParsedTargetsCollision.bad CommitmentRootTargets.pred Qtot)
      emptyTable tr)
    (htable : TraceTable.replay (emptyTable : Table (Addr L) State) represented =
      tableBefore emptyTable tr
        (CommitmentRootFrames.foldedAddr state root tail htail hframe)) :
    (fun slots => recoverAt 0x72 128 represented slots root) =
      (fun slots => recoverAt 0x72 128 tr slots root) := by
  obtain ⟨pre, value, post, htr, hfirst⟩ :=
    FirstReadCut.first_read_cut tr
      (CommitmentRootFrames.foldedAddr state root tail htail hframe) hread
  subst tr
  have hreshape :
      ((pre ++ [(CommitmentRootFrames.foldedAddr state root tail htail hframe, value)]) ++ post) =
        pre ++ (CommitmentRootFrames.foldedAddr state root tail htail hframe, value) :: post := by
    simp [List.append_assoc]
  have hcons' : ∀ q ∈ ((pre ++ [(CommitmentRootFrames.foldedAddr state root tail htail hframe, value)]) ++ post),
      q.2 = H q.1 := by
    simpa only [hreshape] using hcons
  have hQ' : firstReads emptyTable
      ((pre ++ [(CommitmentRootFrames.foldedAddr state root tail htail hframe, value)]) ++ post) ≤ Qtot := by
    simpa only [hreshape] using hQ
  have hnoColl' : ¬ hitsBad (badColl p Qtot) emptyTable
      ((pre ++ [(CommitmentRootFrames.foldedAddr state root tail htail hframe, value)]) ++ post) := by
    simpa only [hreshape] using hnoColl
  have hnoChild' : ¬ hitsBad (ParsedTargetsCollision.bad MerkleChildTargets.pred Qtot)
      emptyTable ((pre ++ [(CommitmentRootFrames.foldedAddr state root tail htail hframe, value)]) ++ post) := by
    simpa only [hreshape] using hnoChild
  have hnoRoot' : ¬ hitsBad (ParsedTargetsCollision.bad CommitmentRootTargets.pred Qtot)
      emptyTable ((pre ++ [(CommitmentRootFrames.foldedAddr state root tail htail hframe, value)]) ++ post) := by
    simpa only [hreshape] using hnoRoot
  have hfullStable := LaterCommitmentStability.folded_word_stable p Qtot H pre post
    state tail htail hframe root value hsize hnode hcons' hQ' hnoColl' hnoChild' hnoRoot'
  funext slots
  have hrepresentedStable := CanonicalTableRecovery.represented_before_cut p Qtot H
    pre post represented
    (CommitmentRootFrames.foldedAddr state root tail htail hframe) value hfirst
    hcons hrepresented hQ hnoColl htable 0x72 128 slots root
  have hfullAt : recoverAt 0x72 128 pre slots root =
      recoverAt 0x72 128
        (pre ++ (CommitmentRootFrames.foldedAddr state root tail htail hframe, value) :: post)
        slots root := by
    simpa only [hreshape] using congrFun hfullStable slots
  exact hrepresentedStable.symm.trans hfullAt

#print axioms c2_table_word_of_read
#print axioms folded_table_word_of_read

end AspisR1.LaterTableStability
