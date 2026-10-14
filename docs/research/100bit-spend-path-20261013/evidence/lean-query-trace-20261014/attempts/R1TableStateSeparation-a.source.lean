import R1DuplexPrefixTable

/-! State values stored before an endpoint differ from the endpoint output. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.TableStateSeparation

open FS FS2 FS2.Duplex
open AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.DuplexFrames
open AspisV8R19.SourceDuplexStep

variable {M Cv : Type} {L : Nat}

theorem known_ne_endpoint (p : Params M Cv L) (H : Addr L → State)
    (tr : List (Addr L × State)) (Qtot : Nat)
    (hcons : ∀ q ∈ tr, q.2 = H q.1)
    (hQ : firstReads emptyTable tr ≤ Qtot)
    (hcoll : ¬ hitsBad (badColl p Qtot) emptyTable tr)
    (c : Addr L) (hcread : Read tr c) (b : Addr L) (v : State)
    (hcell : tableBefore emptyTable tr c b = some v) :
    v ≠ H c := by
  obtain ⟨hv, hbread⟩ := DuplexPrefixTable.table_consistent H tr hcons c b v hcell
  have hbc : b ≠ c := by
    intro h
    subst c
    have hself := tableBefore_self H tr b hcons
    rw [hself] at hcell
    cases hcell
  have hout : H b ≠ H c :=
    noColl_injective p Qtot H tr hcons hQ hcoll b c hbread hcread hbc
  intro heq
  exact hout (hv.symm.trans heq)

theorem prefix_states_ne_endpoint (p : Params M Cv L) (H : Addr L → State)
    (tr : List (Addr L × State)) (Qtot : Nat)
    (hcons : ∀ q ∈ tr, q.2 = H q.1)
    (hQ : firstReads emptyTable tr ≤ Qtot)
    (hcoll : ¬ hitsBad (badColl p Qtot) emptyTable tr)
    (s : Nat → State) (n : Nat)
    (hstep : ∀ j < n, s (j + 1) = H (advanceA p (s j)))
    (hreadadv : ∀ j < n, Read tr (advanceA p (s j)))
    (a c : Addr L) (haread : Read tr a) (hcread : Read tr c)
    (hroot : s 0 = H a)
    (hprefix : c.toBytes.take 32 = bytes (s n)) :
    ∀ j < n, s j ≠ H c := by
  have hcells := DuplexPrefixTable.table_cells p H tr Qtot hcons hQ hcoll
    s n hstep hreadadv c a hcread haread hprefix hroot
  intro j hj
  by_cases hj0 : j = 0
  · subst j
    have hne := known_ne_endpoint p H tr Qtot hcons hQ hcoll c hcread a
      (s 0) hcells.1
    simpa only [hroot] using hne
  · have hjpos : 0 < j := by omega
    have hi : j - 1 < n := by omega
    have hcell := hcells.2 (j - 1) hi
    have hcell' : tableBefore emptyTable tr c (advanceA p (s (j - 1))) = some (s j) := by
      simpa [Nat.sub_add_cancel (show 1 ≤ j by omega)] using hcell
    exact known_ne_endpoint p H tr Qtot hcons hQ hcoll c hcread
      (advanceA p (s (j - 1))) (s j) hcell'

#print axioms known_ne_endpoint
#print axioms prefix_states_ne_endpoint

end AspisR1.TableStateSeparation
end
