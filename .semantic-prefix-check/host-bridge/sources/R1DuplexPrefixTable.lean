import R1DuplexOrder

/-! Consequences of the collision event for cells before a transcript endpoint. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.DuplexPrefixTable

open FS FS2 FS2.Duplex
open AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.DuplexFrames
open AspisV8R19.SourceDuplexStep

variable {M Cv : Type} {L : Nat}

theorem before_endpoint (p : Params M Cv L) (H : Addr L → State)
    (tr : List (Addr L × State)) (Qtot : Nat)
    (hcons : ∀ q ∈ tr, q.2 = H q.1)
    (hQ : firstReads emptyTable tr ≤ Qtot)
    (hcoll : ¬ hitsBad (badColl p Qtot) emptyTable tr)
    (s : Nat → State) (n : Nat)
    (hstep : ∀ j < n, s (j + 1) = H (advanceA p (s j)))
    (hread : ∀ j < n, Read tr (advanceA p (s j)))
    (c : Addr L) (hcread : Read tr c)
    (hprefix : c.toBytes.take 32 = bytes (s n)) :
    ∀ j < n, Before tr (advanceA p (s j)) c := by
  intro j hj
  have hlast : Before tr (advanceA p (s (n - 1))) c := by
    have hn : 0 < n := by omega
    have hlastread : Read tr (advanceA p (s (n - 1))) := hread (n - 1) (by omega)
    have hlaststep : s n = H (advanceA p (s (n - 1))) := by
      simpa [Nat.sub_add_cancel (show 1 ≤ n by omega)] using hstep (n - 1) (by omega)
    have hp : c.toBytes.take 32 = bytes (H (advanceA p (s (n - 1)))) := by
      rw [← hlaststep]
      exact hprefix
    exact noColl_prefix_after p Qtot H tr hcons hQ hcoll
      (advanceA p (s (n - 1))) c hlastread hcread hp
  by_cases hlastj : j = n - 1
  · simpa [hlastj] using hlast
  · have hmid := AspisR1.DuplexOrder.advance_before p H tr Qtot hcons hQ hcoll
      s n hstep hread j (n - 1) (by omega) (by omega)
    exact before_trans tr hmid hlast

theorem table_consistent (H : Addr L → State) (tr : List (Addr L × State))
    (hcons : ∀ q ∈ tr, q.2 = H q.1) (c b : Addr L) (v : State)
    (hcell : tableBefore emptyTable tr c b = some v) :
    v = H b ∧ Read tr b := by
  rw [tableBefore_eq H tr emptyTable c b hcons] at hcell
  split at hcell
  · rename_i hb
    exact ⟨(Option.some.inj hcell).symm, hb.1⟩
  · simp [emptyTable] at hcell

theorem table_cells (p : Params M Cv L) (H : Addr L → State)
    (tr : List (Addr L × State)) (Qtot : Nat)
    (hcons : ∀ q ∈ tr, q.2 = H q.1)
    (hQ : firstReads emptyTable tr ≤ Qtot)
    (hcoll : ¬ hitsBad (badColl p Qtot) emptyTable tr)
    (s : Nat → State) (n : Nat)
    (hstep : ∀ j < n, s (j + 1) = H (advanceA p (s j)))
    (hread : ∀ j < n, Read tr (advanceA p (s j)))
    (c a : Addr L) (hcread : Read tr c) (haread : Read tr a)
    (hprefix : c.toBytes.take 32 = bytes (s n))
    (hroot : s 0 = H a) :
    tableBefore emptyTable tr c a = some (s 0) ∧
      ∀ j < n, tableBefore emptyTable tr c (advanceA p (s j)) = some (s (j + 1)) := by
  have hrootbefore : Before tr a c := by
    by_cases hn : n = 0
    · subst n
      exact noColl_prefix_after p Qtot H tr hcons hQ hcoll a c haread hcread (by
        simpa [hroot] using hprefix)
    · have hnpos : 0 < n := by omega
      have hfirst : Read tr (advanceA p (s 0)) := hread 0 hnpos
      have hp : (advanceA p (s 0)).toBytes.take 32 = bytes (H a) := by
        rw [toBytes_advanceA, ← hroot]
      have hafirst := noColl_prefix_after p Qtot H tr hcons hQ hcoll
        a (advanceA p (s 0)) haread hfirst hp
      have hfirstc := before_endpoint p H tr Qtot hcons hQ hcoll s n hstep hread
        c hcread hprefix 0 hnpos
      exact before_trans tr hafirst hfirstc
  constructor
  · rw [tableBefore_eq H tr emptyTable c a hcons, if_pos hrootbefore]
    exact congrArg some hroot.symm
  · intro j hj
    have hb := before_endpoint p H tr Qtot hcons hQ hcoll s n hstep hread c hcread hprefix j hj
    rw [tableBefore_eq H tr emptyTable c (advanceA p (s j)) hcons, if_pos hb]
    exact congrArg some (hstep j hj).symm

#print axioms before_endpoint
#print axioms table_consistent
#print axioms table_cells

end AspisR1.DuplexPrefixTable
end
