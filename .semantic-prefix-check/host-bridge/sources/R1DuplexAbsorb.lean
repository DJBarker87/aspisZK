import R1DuplexRewind

/-! Deterministic absorb-cell uniqueness and separation from advance cells.
This module does not add assumptions to the existing duplex collision model. -/

set_option autoImplicit false
noncomputable section
namespace AspisR1.DuplexAbsorb

open FS FS2 FS2.Duplex
open AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.DuplexFrames
open AspisV8R19.SourceDuplexStep

variable {M Cv : Type} {L : Nat}

theorem parseAbsorb_advance_none (p : Params M Cv L) (s : State) :
    parseAbsorb (advanceA p s) = none := by
  have hlen : (advanceA p s).toBytes.length = 33 := by
    simp [advanceA, Addr.toBytes_ofBytes, advance, bytes_length]
  simp only [parseAbsorb, hlen]
  simp

theorem theUnique_empty {α : Type} [Fintype α] [DecidableEq α] :
    theUnique (∅ : Finset α) = none := by
  classical
  simp [theUnique]

theorem unique_absorb (p : Params M Cv L) (T : Table (Addr L) State)
    (H : Addr L → State) (tr : List (Addr L × State)) (Qtot : Nat)
    (hcons : ∀ q ∈ tr, q.2 = H q.1)
    (hQ : firstReads emptyTable tr ≤ Qtot)
    (hcoll : ¬ hitsBad (badColl p Qtot) emptyTable tr)
    (hT : ∀ a v, T a = some v → v = H a ∧ Read tr a)
    (a : Addr L) (hparse : (parseAbsorb a).isSome)
    (hcell : T a = some (H a)) :
    theUnique (absCells T (H a)) = some a := by
  apply theUnique_cellsWith T (H a) (fun b => (parseAbsorb b).isSome) a
  intro b
  constructor
  · rintro ⟨hbcell, hbparse⟩
    have ⟨hvalue, hread⟩ := hT b (H a) hbcell
    have ⟨_, haread⟩ := hT a (H a) hcell
    have houtputs : H b = H a := hvalue.symm
    by_cases hba : b = a
    · exact hba
    · have hne : b ≠ a := hba
      exact False.elim ((noColl_injective p Qtot H tr hcons hQ hcoll
        b a hread haread hne) houtputs)
  · intro hba
    subst b
    exact ⟨hcell, hparse⟩

theorem absCells_advance_empty (p : Params M Cv L) (T : Table (Addr L) State)
    (H : Addr L → State) (tr : List (Addr L × State)) (Qtot : Nat)
    (hcons : ∀ q ∈ tr, q.2 = H q.1)
    (hQ : firstReads emptyTable tr ≤ Qtot)
    (hcoll : ¬ hitsBad (badColl p Qtot) emptyTable tr)
    (hT : ∀ a v, T a = some v → v = H a ∧ Read tr a)
    (s : State)
    (hcell : T (advanceA p s) = some (H (advanceA p s))) :
    absCells T (H (advanceA p s)) = ∅ := by
  classical
  ext a
  have hempty : (a ∈ (∅ : Finset (Addr L))) = False := by simp
  rw [hempty]
  simp only [absCells, cellsWith, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro ha
    have ⟨hcellA, hparseA⟩ :
        T a = some (H (advanceA p s)) ∧ (parseAbsorb a).isSome := by
      simpa [absCells, cellsWith] using ha
    have ⟨hvalueA, hreadA⟩ := hT a (H (advanceA p s)) hcellA
    have ⟨_, hreadAdvance⟩ := hT (advanceA p s)
      (H (advanceA p s)) hcell
    have houtputs : H a = H (advanceA p s) := hvalueA.symm
    by_cases haddr : a = advanceA p s
    · subst a
      rw [parseAbsorb_advance_none] at hparseA
      simp at hparseA
    · have hne : a ≠ advanceA p s := haddr
      exact False.elim ((noColl_injective p Qtot H tr hcons hQ hcoll
        a (advanceA p s) hreadA hreadAdvance hne) houtputs)
  · intro hfalse
    exact False.elim hfalse

#print axioms parseAbsorb_advance_none
#print axioms theUnique_empty
#print axioms unique_absorb
#print axioms absCells_advance_empty

end AspisR1.DuplexAbsorb
end
