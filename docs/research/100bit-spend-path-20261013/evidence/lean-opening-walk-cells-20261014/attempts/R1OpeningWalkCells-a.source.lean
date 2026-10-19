import R1OpeningWalk
import R1ReseedSeparation
import R1DuplexRewind

/-! Turn the concrete absorb/advance table cells into the generic opening walk. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OpeningWalkCells

open FS FS2 FS2.Duplex
open AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.DuplexFrames
open AspisV8R19.SourceDuplexStep

variable {M Cv : Type} {L : Nat}

theorem walk_of_cells (p : Params M Cv L) (pubBytes : Bytes) (tag : Byte)
    (T : Table (Addr L) State) (semanticFuel : Nat)
    (H : Addr L → State) (tr : List (Addr L × State)) (Qtot : Nat)
    (hcons : ∀ q ∈ tr, q.2 = H q.1)
    (hQ : firstReads emptyTable tr ≤ Qtot)
    (hold : ¬ hitsBad (badColl p Qtot) emptyTable tr)
    (hT : ∀ b v, T b = some v → v = H b ∧ Read tr b)
    (fuel n : Nat) (hle : n ≤ fuel)
    (s absorbed : Nat → State) (label : Nat → Byte) (data : Nat → Bytes)
    (hD : ∀ j, (data j).length ≤ p.D)
    (habs : ∀ j, j < n → absorbed j =
      H (absorbA p (s j) (label j) (data j) (hD j)))
    (hstep : ∀ j, j < n → s (j + 1) = H (advanceA p (absorbed j)))
    (ha : ∀ j, j < n →
      T (absorbA p (s j) (label j) (data j) (hD j)) = some (absorbed j))
    (had : ∀ j, j < n →
      T (advanceA p (absorbed j)) = some (s (j + 1)))
    (c1 : State) (pre : List InitialWalk.RawRec)
    (hbase : ReseedPrefix.decode p pubBytes tag T semanticFuel (s 0) =
      some (c1, pre)) :
    OpeningWalk.walk p T (ReseedPrefix.decode p pubBytes tag T semanticFuel)
      fuel (s n) =
        some (c1, pre ++ InitialWalk.records s absorbed label data n) := by
  apply OpeningWalk.walk_of_lookups p T
    (ReseedPrefix.decode p pubBytes tag T semanticFuel) fuel n
    s absorbed label data c1 pre hle
  · intro j hj
    have habsCell : T (absorbA p (s j) (label j) (data j) (hD j)) =
        some (H (absorbA p (s j) (label j) (data j) (hD j))) := by
      rw [habs j hj]
      exact ha j hj
    have hnextCell : T (advanceA p (s j)) =
        some (H (advanceA p (s j))) := by
      simpa only [hstep j hj] using had j hj
    exact DuplexRewind.unique_advance p T H tr Qtot hcons hQ hold
      (s j) hnextCell hT
  · intro j hj
    have habsCell : T (absorbA p (s j) (label j) (data j) (hD j)) =
        some (H (absorbA p (s j) (label j) (data j) (hD j))) := by
      rw [habs j hj]
      exact ha j hj
    have hfind := ReseedBoundary.findCell_correct p H tr Qtot hcons hQ hold
      T hT (absorbA p (s j) (label j) (data j) (hD j)) habsCell
    rw [habs j hj] at hfind
    exact ⟨absorbA p (s j) (label j) (data j) (hD j), hfind, rfl⟩
  · exact hbase
  · intro j hj hjle
    have hjpos : 0 < j := hj
    have hpred : j - 1 < n := by omega
    have hpredCell : T (advanceA p (absorbed (j - 1))) =
        some (H (advanceA p (absorbed (j - 1)))) := by
      simpa only [hstep (j - 1) hpred] using had (j - 1) hpred
    have hnone := ReseedSeparation.decode_advance_none p pubBytes tag T
      semanticFuel H tr Qtot hcons hQ hold hT (absorbed (j - 1)) hpredCell
    have hstate : s j = H (advanceA p (absorbed (j - 1))) := by
      simpa only [Nat.sub_add_cancel (by omega : 1 ≤ j)] using
        hstep (j - 1) hpred
    simpa only [hstate] using hnone

#print axioms walk_of_cells
end AspisR1.OpeningWalkCells
end
