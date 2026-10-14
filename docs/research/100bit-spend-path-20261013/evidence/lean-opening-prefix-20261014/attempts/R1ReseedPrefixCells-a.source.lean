import R1ReseedPrefix

/-! Table-cell form of the semantic-prefix recovery. Later ordinary opening
rows may already be present; no first-read position is assumed in this lemma. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.ReseedPrefixCells
open FS FS2 FS2.Duplex
open AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.DuplexFrames
open AspisV8R19.SourceDuplexStep
variable {M Cv : Type} {L : Nat}

theorem decode_of_cells (p : Params M Cv L)
    (pubBytes : Bytes) (hlen : pubBytes.length < 2^32)
    (hL : 75 + pubBytes.length ≤ L) (c1 : State) (tag : Byte) (h62 : 62 ≤ L)
    (H : Addr L → State) (tr : List (Addr L × State)) (Qtot : Nat)
    (hcons : ∀ q ∈ tr, q.2 = H q.1) (hQ : firstReads emptyTable tr ≤ Qtot)
    (hold : ¬ hitsBad (badColl p Qtot) emptyTable tr)
    (T : Table (Addr L) State)
    (hT : ∀ a v, T a = some v → v = H a ∧ Read tr a)
    (fuel n : Nat) (hn : 0 < n) (hle : n ≤ fuel)
    (s absorbed : Nat → State) (label : Nat → Byte) (data : Nat → Bytes)
    (hD : ∀ j, (data j).length ≤ p.D)
    (hroot : s 0 = H (PublicInitFrame.addr pubBytes hL c1))
    (habs : ∀ j < n, absorbed j = H (absorbA p (s j) (label j) (data j) (hD j)))
    (hstep : ∀ j < n, s (j + 1) = H (advanceA p (absorbed j)))
    (hi : T (PublicInitFrame.addr pubBytes hL c1) = some (s 0))
    (ha : ∀ j < n, T (absorbA p (s j) (label j) (data j) (hD j)) = some (absorbed j))
    (had : ∀ j < n, T (advanceA p (absorbed j)) = some (s (j + 1)))
    (hr : T (OpeningReseedFrame.addr tag h62 (s n)) =
      some (H (OpeningReseedFrame.addr tag h62 (s n)))) :
    ReseedPrefix.decode p pubBytes tag T fuel (H (OpeningReseedFrame.addr tag h62 (s n))) =
      some (c1, CarryLast.apply (H (OpeningReseedFrame.addr tag h62 (s n)))
        (InitialWalk.records s absorbed label data n)) := by
  apply ReseedPrefix.decode_of_raw
  have hrw := StrictReseedDecoder.recover_of_cell p H tr Qtot hcons hQ hold T hT
    tag h62 (s n) hr
  have hw := InitialWalkCells.walk_of_cells p pubBytes hlen hL c1 H tr Qtot hcons hQ hold
    T hT fuel n hn hle s absorbed label data hD hroot habs hstep hi ha had
  simp only [ReseedPrefix.raw, hrw]
  exact hw

#print axioms decode_of_cells
end AspisR1.ReseedPrefixCells
end
