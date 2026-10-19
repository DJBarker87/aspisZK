import R1InitialWalk
import R1PublicInitBoundaryFacts
import R1DuplexRewind

/-! Derive all structural-walker lookups from actual consistent table cells.
The decoder does not receive the oracle or an oracle-dependent initial state.
It stops only after parsing the fixed public bytes and the C1 root. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.InitialWalkCells
open FS FS2 FS2.Duplex
open AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.DuplexFrames
open AspisV8R19.SourceDuplexStep
variable {M Cv : Type} {L : Nat}

theorem walk_of_cells (p : Params M Cv L)
    (pubBytes : Bytes) (hlen : pubBytes.length < 2^32)
    (hL : 75 + pubBytes.length ≤ L) (c1 : State)
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
    (had : ∀ j < n, T (advanceA p (absorbed j)) = some (s (j + 1))) :
    InitialWalk.walk p pubBytes T fuel (s n) =
      some (c1, InitialWalk.records s absorbed label data n) := by
  apply InitialWalk.walk_of_lookups p pubBytes T fuel n s absorbed label data c1 hn hle
  · intro j hj
    rw [hstep j hj]
    apply DuplexRewind.unique_advance p T H tr Qtot hcons hQ hold (absorbed j)
    · simpa only [hstep j hj] using had j hj
    · exact hT
  · intro j hj
    refine ⟨absorbA p (s j) (label j) (data j) (hD j), ?_, parseAbsorb_absorbA ..⟩
    rw [habs j hj]
    apply ReseedBoundary.findCell_correct p H tr Qtot hcons hQ hold T hT
    simpa only [habs j hj] using ha j hj
  · have hi' : T (PublicInitFrame.addr pubBytes hL c1) =
        some (H (PublicInitFrame.addr pubBytes hL c1)) := by
      simpa only [hroot] using hi
    have hf := ReseedBoundary.findCell_correct p H tr Qtot hcons hQ hold T hT
      (PublicInitFrame.addr pubBytes hL c1) hi'
    simp only [InitialWalk.rootAt, hroot, hf, PublicInitParse.parse_addr pubBytes hlen hL c1]
  · intro j hj hjn
    have hprev : j - 1 < n := by omega
    have hs : s j = H (advanceA p (absorbed (j - 1))) := by
      simpa only [Nat.sub_add_cancel (show 1 ≤ j by omega)] using hstep (j - 1) hprev
    have hc : T (advanceA p (absorbed (j - 1))) =
        some (H (advanceA p (absorbed (j - 1)))) := by
      simpa only [hstep (j - 1) hprev] using had (j - 1) hprev
    have hf := ReseedBoundary.findCell_correct p H tr Qtot hcons hQ hold T hT
      (advanceA p (absorbed (j - 1))) hc
    simp only [InitialWalk.rootAt, hs, hf, PublicInitBoundaryFacts.parse_advance_none]

#print axioms walk_of_cells
end AspisR1.InitialWalkCells
end
