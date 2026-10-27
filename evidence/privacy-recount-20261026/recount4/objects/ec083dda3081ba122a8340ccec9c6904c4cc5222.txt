import R1Z.ProverCommitSeedJoin19
/-! Fixed five-draw exhaustion accounting. The probability theorem is for
uniform independent finite words. Connecting those words to the retained
shared source oracle is a separate execution obligation. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitFuelMass22
open R0Z R0Z.FsStatement R0Z.FsAbort R0Z.FsGood R0Z.HvzkV
attribute [local instance] Classical.propDecidable

def k : Nat := 5
def count : Nat := 24
def p : Nat := 2147483647

def exhausted {U : Type} (zero : U) (draws : Fin k → U) : Prop := ∀ i, draws i = zero

theorem exhaustion_mass {U : Type} [Fintype U] (zero : U) :
    eventMass (exhausted zero) = 1 / (Fintype.card U : ℚ)^k := by
  have he : exhausted zero = fun draws : Fin k → U => draws = fun _ => zero := by
    funext draws
    exact propext ⟨fun h => funext h, fun h i => congrFun h i⟩
  rw [he,QueryScanSharedHistoryMass.point_mass,Fintype.card_fun,Fintype.card_fin,Nat.cast_pow]

def charge : ℚ := (count : ℚ) / (p : ℚ)^k

theorem charge_le : charge ≤ 1 / (2 : ℚ)^120 := by
  norm_num [charge,count,p,k]

/-- Per-side union charge; neither inter-instance independence nor an
exhaustive enumeration of field elements is required. -/
theorem union_bound {M : Type} [Fintype M] [Nonempty M]
    (failure : Fin count → M → Prop)
    (per_instance : ∀ i, eventMass (failure i) ≤ 1 / (p : ℚ)^k) :
    eventMass (fun m => ∃ i, failure i m) ≤ charge := by
  have h := R0Z.FsAbortBounds.mass_exists_le_card failure (1 / (p : ℚ)^k)
    (fun i => by simpa only [R0Z.FsAbortBounds.mass,eventMass] using per_instance i)
  simpa only [R0Z.FsAbortBounds.mass,eventMass,Fintype.card_fin,charge,div_eq_mul_inv,one_mul] using h

/-- Enlarge the already seed-augmented fixed bad events once, on attempt 0. -/
def augmented {M : Type} (old : Fin 8 → M → Prop)
    (failure : Fin count → M → Prop) (i : Fin 8) (m : M) : Prop :=
  old i m ∨ (i = 0 ∧ ∃ j, failure j m)

theorem old_contained {M : Type} (old : Fin 8 → M → Prop)
    (failure : Fin count → M → Prop) (i : Fin 8) (m : M) (h : old i m) :
    augmented old failure i m := Or.inl h

theorem augmented_mass {M : Type} [Fintype M] [Nonempty M]
    (old : Fin 8 → M → Prop) (failure : Fin count → M → Prop)
    (per_instance : ∀ i, eventMass (failure i) ≤ 1 / (p : ℚ)^k) :
    eventMass (fun m => ∃ i, augmented old failure i m) ≤
      eventMass (fun m => ∃ i, old i m) + charge := by
  have sub : ∀ m, (∃ i, augmented old failure i m) →
      (∃ i, old i m) ∨ ∃ j, failure j m := by
    rintro m ⟨i, ho | ⟨_,hf⟩⟩
    · exact Or.inl ⟨i,ho⟩
    · exact Or.inr hf
  exact ((eventMass_mono _ _ sub).trans (R0Z.FsAbortBounds.mass_or_le _ _)).trans
    (add_le_add (le_refl _) (union_bound failure per_instance))

theorem total_lt_target {q r : Nat} (hq : q ≤ 2^65) (hr : r ≤ 2^64) :
    1 / (2 : ℚ)^109 + 1 / (2 : ℚ)^137 + 1 / (2 : ℚ)^454 +
      QueryScanFreshUnion.freshBudget q + 2 * ProverCommitSeedEvent19.budget r +
      2 * charge < 1 / (2 : ℚ)^100 := by
  have h137 := QueryScanHistoryRealNumerics.dyadic_mono (by omega : 109 ≤ 137)
  have h454 := QueryScanHistoryRealNumerics.dyadic_mono (by omega : 109 ≤ 454)
  have hf := QueryScanFreshNumerics.fresh_budget_small hq
  have hs : ProverCommitSeedEvent19.budget r ≤ 1 / (2 : ℚ)^109 :=
    (ProverCommitSeedEvent19.budget_mono hr).trans (by
      rw [ProverCommitSeedJoin19.budget_pow64]
      exact QueryScanHistoryRealNumerics.dyadic_mono (by omega : 109 ≤ 192))
  have hc := charge_le.trans (QueryScanHistoryRealNumerics.dyadic_mono (by omega : 109 ≤ 120))
  have hsum : 1 / (2 : ℚ)^109 + 1 / (2 : ℚ)^137 + 1 / (2 : ℚ)^454 +
      QueryScanFreshUnion.freshBudget q + 2 * ProverCommitSeedEvent19.budget r +
      2 * charge ≤ 10 / (2 : ℚ)^109 := by
    have hp : 0 ≤ 1 / (2 : ℚ)^109 := by positivity
    linarith
  apply hsum.trans_lt
  norm_num

#print axioms exhaustion_mass
#print axioms charge_le
#print axioms union_bound
#print axioms old_contained
#print axioms augmented_mass
#print axioms total_lt_target
end R1Z.ProverCommitFuelMass22
