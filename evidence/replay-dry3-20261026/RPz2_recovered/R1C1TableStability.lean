import R1CanonicalTableRecovery
import R1C1BeforeFrameStability
import R1FirstReadCut

/-! C1 recovery can be compared through the finite table at the first
initialization-frame read. The table identity is an explicit premise here. -/
set_option autoImplicit false
namespace AspisR1.C1TableStability

open FS FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open AspisR1.CanonicalRecoveryStability

variable {M Cv : Type} {L : Nat}

theorem c1_table_word_stable (p : Params M Cv L) (Qtot : Nat)
    (H : Addr L → State) (pre post represented : List (Addr L × State))
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
    (hrepresented : ∀ q ∈ represented, q.2 = H q.1)
    (hfirst : PublicInitFrame.addr pubBytes hframe root ∉ pre.map Prod.fst)
    (htable : TraceTable.replay emptyTable represented =
      tableBefore emptyTable
        ((pre ++ [(PublicInitFrame.addr pubBytes hframe root, answer)]) ++ post)
        (PublicInitFrame.addr pubBytes hframe root)) :
    (fun slots => recoverAt 0x71 480 represented slots root) =
      (fun slots => recoverAt 0x71 480
        ((pre ++ [(PublicInitFrame.addr pubBytes hframe root, answer)]) ++ post)
        slots root) := by
  have hconsCut : ∀ q ∈ pre ++ (PublicInitFrame.addr pubBytes hframe root, answer) :: post,
      q.2 = H q.1 := by
    simpa [List.append_assoc] using hcons
  have hQCut : firstReads emptyTable
      (pre ++ (PublicInitFrame.addr pubBytes hframe root, answer) :: post) ≤ Qtot := by
    simpa [List.append_assoc] using hQ
  have hnoCollCut : ¬ hitsBad (badColl p Qtot) emptyTable
      (pre ++ (PublicInitFrame.addr pubBytes hframe root, answer) :: post) := by
    simpa [List.append_assoc] using hnoColl
  have htableCut : TraceTable.replay emptyTable represented =
      tableBefore emptyTable
        (pre ++ (PublicInitFrame.addr pubBytes hframe root, answer) :: post)
        (PublicInitFrame.addr pubBytes hframe root) := by
    simpa [List.append_assoc] using htable
  have hcut := CanonicalTableRecovery.represented_before_cut p Qtot H
    pre post represented (PublicInitFrame.addr pubBytes hframe root) answer
    hfirst hconsCut hrepresented hQCut hnoCollCut htableCut 0x71 480
  have hpre : (fun slots => recoverAt 0x71 480 pre slots root) =
      (fun slots => recoverAt 0x71 480 represented slots root) := by
    funext slots
    exact hcut slots root
  calc
    (fun slots => recoverAt 0x71 480 represented slots root) =
        (fun slots => recoverAt 0x71 480 pre slots root) := hpre.symm
    _ = fun slots => recoverAt 0x71 480
        ((pre ++ [(PublicInitFrame.addr pubBytes hframe root, answer)]) ++ post)
        slots root :=
      C1BeforeFrameStability.c1_word_stable p Qtot H pre post pubBytes hframe
        root answer hsize hnode hcons hQ hnoColl hnoChild hnoRoot

theorem c1_table_word_of_read (p : Params M Cv L) (Qtot : Nat)
    (H : Addr L → State) (tr represented : List (Addr L × State))
    (pubBytes : Bytes) (hframe : 75 + pubBytes.length ≤ L)
    (root : State) (hsize : 514 ≤ L) (hnode : 257 ≤ L)
    (hcons : ∀ q ∈ tr, q.2 = H q.1)
    (hQ : firstReads emptyTable tr ≤ Qtot)
    (hnoColl : ¬ hitsBad (badColl p Qtot) emptyTable tr)
    (hnoChild : ¬ hitsBad (ParsedTargetsCollision.bad MerkleChildTargets.pred Qtot)
      emptyTable tr)
    (hnoRoot : ¬ hitsBad (ParsedTargetsCollision.bad CommitmentRootTargets.pred Qtot)
      emptyTable tr)
    (hrepresented : ∀ q ∈ represented, q.2 = H q.1)
    (hread : Read tr (PublicInitFrame.addr pubBytes hframe root))
    (htable : TraceTable.replay emptyTable represented =
      tableBefore emptyTable tr (PublicInitFrame.addr pubBytes hframe root)) :
    (fun slots => recoverAt 0x71 480 represented slots root) =
      (fun slots => recoverAt 0x71 480 tr slots root) := by
  let frame := PublicInitFrame.addr pubBytes hframe root
  obtain ⟨pre, answer, post, hrep, hfirst⟩ :=
    FirstReadCut.first_read_cut tr frame hread
  have hcons' : ∀ q ∈ (pre ++ [(frame, answer)]) ++ post, q.2 = H q.1 := by
    intro q hq
    apply hcons q
    simpa [hrep] using hq
  have hQ' : firstReads emptyTable ((pre ++ [ (frame, answer) ]) ++ post) ≤ Qtot := by
    simpa [hrep] using hQ
  have hnoColl' : ¬ hitsBad (badColl p Qtot) emptyTable
      ((pre ++ [ (frame, answer) ]) ++ post) := by
    simpa [hrep] using hnoColl
  have hnoChild' : ¬ hitsBad (ParsedTargetsCollision.bad MerkleChildTargets.pred Qtot)
      emptyTable ((pre ++ [ (frame, answer) ]) ++ post) := by
    simpa [hrep] using hnoChild
  have hnoRoot' : ¬ hitsBad (ParsedTargetsCollision.bad CommitmentRootTargets.pred Qtot)
      emptyTable ((pre ++ [ (frame, answer) ]) ++ post) := by
    simpa [hrep] using hnoRoot
  have htable' : TraceTable.replay emptyTable represented =
      tableBefore emptyTable ((pre ++ [(frame, answer)]) ++ post) frame := by
    simpa [hrep] using htable
  have hstable := c1_table_word_stable p Qtot H pre post represented pubBytes hframe
    root answer hsize hnode hcons' hQ' hnoColl' hnoChild' hnoRoot' hrepresented hfirst htable'
  simpa [hrep] using hstable

#print axioms c1_table_word_stable
#print axioms c1_table_word_of_read

end AspisR1.C1TableStability
