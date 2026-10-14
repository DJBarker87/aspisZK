import R1TraceTableMembership
import R1CanonicalLogMembership
import R1CanonicalLogSeparation
import R1MerkleLogExt
import R1CanonicalRecoveryStability

/-! Canonical recovery depends on the represented oracle table, not on the
ordering or duplication of consistent records. The needed hash separation
is derived from the existing full-trace collision exclusion. -/
set_option autoImplicit false
namespace AspisR1.CanonicalTableRecovery

open FS FS2.Duplex
open AspisV8R19.SourceDuplexStep AspisV8R19.DuplexFrames
open AspisV8R19.MemoizedProgramLaw
open CanonicalByteHash CanonicalRecoveryStability

variable {M Cv : Type} {L : Nat}

theorem recover_eq_of_replay_eq (p : Params M Cv L) (Qtot : Nat)
    (H : Addr L → State) (pre represented tr : List (Addr L × State))
    (hpre : ∀ q ∈ pre, q.2 = H q.1)
    (hrepresented : ∀ q ∈ represented, q.2 = H q.1)
    (hcons : ∀ q ∈ tr, q.2 = H q.1)
    (hread : ∀ a, Read pre a → Read tr a)
    (hQ : firstReads emptyTable tr ≤ Qtot)
    (hno : ¬ hitsBad (badColl p Qtot) emptyTable tr)
    (heq : TraceTable.replay emptyTable pre = TraceTable.replay emptyTable represented)
    (tag : Merkle32Path.Byte) (width : Nat) (slots : List (Fin 8)) (root : State) :
    recoverAt tag width pre slots root = recoverAt tag width represented slots root := by
  have hraw := TraceTableMembership.mem_eq_of_replay_eq H pre represented
    hpre hrepresented heq
  have hlogs := CanonicalLogMembership.byteLog_mem_eq pre represented hraw
  exact MerkleLogExt.recover_eq (hashBytes H)
    (CanonicalOracleLog.byteLog pre) (CanonicalOracleLog.byteLog represented)
    (CanonicalOracleLog.consistent H pre hpre)
    (CanonicalLogSeparation.separated p Qtot H pre tr hcons hread hQ hno)
    hlogs tag width slots root

theorem represented_before_cut (p : Params M Cv L) (Qtot : Nat)
    (H : Addr L → State) (pre post represented : List (Addr L × State))
    (a : Addr L) (value : State)
    (hfirst : a ∉ pre.map Prod.fst)
    (hcons : ∀ q ∈ pre ++ (a, value) :: post, q.2 = H q.1)
    (hrepresented : ∀ q ∈ represented, q.2 = H q.1)
    (hQ : firstReads emptyTable (pre ++ (a, value) :: post) ≤ Qtot)
    (hno : ¬ hitsBad (badColl p Qtot) emptyTable (pre ++ (a, value) :: post))
    (htable : TraceTable.replay emptyTable represented =
      tableBefore emptyTable (pre ++ (a, value) :: post) a)
    (tag : Merkle32Path.Byte) (width : Nat) (slots : List (Fin 8)) (root : State) :
    recoverAt tag width pre slots root = recoverAt tag width represented slots root := by
  have hpre : ∀ q ∈ pre, q.2 = H q.1 := by
    intro q hq
    exact hcons q (List.mem_append.mpr (Or.inl hq))
  have hread : ∀ b, Read pre b → Read (pre ++ (a, value) :: post) b := by
    intro b hb
    change b ∈ (pre ++ (a, value) :: post).map Prod.fst
    rw [List.map_append]
    exact List.mem_append.mpr (Or.inl hb)
  rw [TraceTable.tableBefore_cut emptyTable pre a value post hfirst] at htable
  exact recover_eq_of_replay_eq p Qtot H pre represented (pre ++ (a, value) :: post)
    hpre hrepresented hcons hread hQ hno htable.symm tag width slots root

#print axioms recover_eq_of_replay_eq
#print axioms represented_before_cut

end AspisR1.CanonicalTableRecovery
