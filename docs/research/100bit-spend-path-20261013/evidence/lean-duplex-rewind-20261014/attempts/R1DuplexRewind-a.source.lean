import FS2.DuplexWalk

/-! Deterministic recovery of a finite state path from unique predecessor
cells in a duplex table. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.DuplexRewind

open FS FS2 FS2.Duplex
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.DuplexFrames
open AspisV8R19.SourceDuplexStep

variable {M Cv : Type} {L : Nat}

def rewind (p : Params M Cv L) (T : Table (Addr L) State) :
    Nat → State → Option (List State)
  | 0, s => some [s]
  | n + 1, s =>
      match theUnique (advPre p T s) with
      | none => none
      | some prev => (rewind p T n prev).map (· ++ [s])

theorem rewind_of_preimages (p : Params M Cv L) (T : Table (Addr L) State)
    (s : Nat → State) (n : Nat)
    (hpre : ∀ j < n, theUnique (advPre p T (s (j + 1))) = some (s j)) :
    rewind p T n (s n) = some ((List.range (n + 1)).map s) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [rewind, hpre n (by omega), ih (by
        intro j hj
        exact hpre j (by omega))]
      simp only [List.range_succ, List.map_append, List.map_singleton]

theorem unique_advance (p : Params M Cv L) (T : Table (Addr L) State)
    (H : Addr L → State) (tr : List (Addr L × State)) (Qtot : Nat)
    (hcons : ∀ q ∈ tr, q.2 = H q.1)
    (hQ : firstReads emptyTable tr ≤ Qtot)
    (hcoll : ¬ hitsBad (badColl p Qtot) emptyTable tr)
    (s : State)
    (hcell : T (advanceA p s) = some (H (advanceA p s)))
    (hT : ∀ a v, T a = some v → v = H a ∧ Read tr a) :
    theUnique (advPre p T (H (advanceA p s))) = some s := by
  apply theUnique_preimages
  intro s'
  constructor
  · intro h
    have ⟨hv, hr⟩ := hT _ _ h
    have ⟨_, hread⟩ := hT _ _ hcell
    have heq : H (advanceA p s') = H (advanceA p s) := hv.symm
    have haddr : advanceA p s' = advanceA p s := by
      by_contra hne
      exact (noColl_injective p Qtot H tr hcons hQ hcoll
        (advanceA p s') (advanceA p s) hr hread hne) heq
    exact advanceA_injective p haddr
  · intro hs
    subst s'
    exact hcell

theorem rewind_of_noColl (p : Params M Cv L) (T : Table (Addr L) State)
    (H : Addr L → State) (tr : List (Addr L × State)) (Qtot n : Nat)
    (hcons : ∀ q ∈ tr, q.2 = H q.1)
    (hQ : firstReads emptyTable tr ≤ Qtot)
    (hcoll : ¬ hitsBad (badColl p Qtot) emptyTable tr)
    (hT : ∀ a v, T a = some v → v = H a ∧ Read tr a)
    (s : Nat → State)
    (hstep : ∀ j < n, s (j + 1) = H (advanceA p (s j)))
    (hcells : ∀ j < n, T (advanceA p (s j)) = some (s (j + 1))) :
    rewind p T n (s n) = some ((List.range (n + 1)).map s) := by
  apply rewind_of_preimages p T s n
  intro j hj
  have hcell : T (advanceA p (s j)) = some (H (advanceA p (s j))) := by
    rw [← hstep j hj]
    exact hcells j hj
  have hu := unique_advance p T H tr Qtot hcons hQ hcoll (s j) hcell hT
  simpa only [hstep j hj] using hu

#print axioms rewind_of_preimages
#print axioms unique_advance
#print axioms rewind_of_noColl

end AspisR1.DuplexRewind
end
