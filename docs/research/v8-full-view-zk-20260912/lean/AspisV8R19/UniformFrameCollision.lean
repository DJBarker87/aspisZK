import AspisV8R19.UniformStateFirstHitMean

/-! One-step collision counting for a fixed uniformly sampled finite state.

The frame is injective and the prior read set is fixed.  This is only a
finite cardinality bound; it does not assert a source law, adaptive
freshness, or any cryptographic property.
-/
set_option autoImplicit false
namespace AspisV8R19.UniformFrameCollision

open OracleResampling UniformStateFirstHitMean
noncomputable section

def hitSet {S I : Type*} [Fintype S] (frame : S → I) (reads : Finset I) : Finset S := by
  classical
  exact Finset.univ.filter (fun s => frame s ∈ reads)

theorem hitSet_card_le {S I : Type*} [Fintype S]
    (frame : S → I) (reads : Finset I) (hinj : Function.Injective frame) :
    (hitSet frame reads).card ≤ reads.card := by
  classical
  apply Finset.card_le_card_of_injOn frame
  · intro s hs
    simpa [hitSet] using hs
  · intro s _ t _ h
    exact hinj h

def hitFraction {S I : Type*} [Fintype S]
    (frame : S → I) (reads : Finset I) : ℚ :=
  (hitSet frame reads).card / (Fintype.card S : ℚ)

theorem hitFraction_le {S I : Type*} [Fintype S] [Nonempty S]
    (frame : S → I) (reads : Finset I) (hinj : Function.Injective frame) :
    hitFraction frame reads ≤ reads.card / (Fintype.card S : ℚ) := by
  unfold hitFraction
  exact div_le_div_of_nonneg_right
    (by exact_mod_cast hitSet_card_le frame reads hinj) (by positivity)

theorem hitFraction_list_le {S I : Type*} [Fintype S] [Nonempty S] [DecidableEq I]
    (frame : S → I) (reads : List I) (hinj : Function.Injective frame) :
    hitFraction frame reads.toFinset ≤ (reads.length : ℚ) / (Fintype.card S : ℚ) := by
  calc
    hitFraction frame reads.toFinset ≤ reads.toFinset.card / (Fintype.card S : ℚ) :=
      hitFraction_le frame reads.toFinset hinj
    _ ≤ (reads.length : ℚ) / (Fintype.card S : ℚ) := by
      exact div_le_div_of_nonneg_right
        (by exact_mod_cast List.toFinset_card_le reads) (by positivity)

def hitIndicator {S I : Type*} [DecidableEq I]
    (frame : S → I) (reads : List I) (s : S) : ℚ :=
  if frame s ∈ reads then 1 else 0

theorem mean_hitIndicator_eq_fraction
    {S I : Type*} [Fintype S] [DecidableEq I]
    (frame : S → I) (reads : List I) :
    mean (hitIndicator frame reads) = hitFraction frame reads.toFinset := by
  unfold mean hitIndicator hitFraction hitSet
  congr 1
  simpa only [List.mem_toFinset] using
    (Finset.sum_boole (R := ℚ) (fun s : S => frame s ∈ reads.toFinset)
      (Finset.univ : Finset S))

theorem mean_hitIndicator_list_le
    {S I : Type*} [Fintype S] [Nonempty S] [DecidableEq I]
    (frame : S → I) (reads : List I) (hinj : Function.Injective frame) :
    mean (hitIndicator frame reads) ≤
      (reads.length : ℚ) / (Fintype.card S : ℚ) := by
  rw [mean_hitIndicator_eq_fraction]
  exact hitFraction_list_le frame reads hinj

#print axioms hitSet_card_le
#print axioms hitFraction_le
#print axioms hitFraction_list_le
#print axioms mean_hitIndicator_eq_fraction
#print axioms mean_hitIndicator_list_le
end
end AspisV8R19.UniformFrameCollision
