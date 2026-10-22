import R1Z.SimCostWriter

/-! The outer firstGood control, distinct from the 24 inner five-word searches.
No tariff for P_R1 is invented: the parameter is the cost of an exact Boolean
decision implementation, not merely a sufficient certificate checker. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.SimCostOuterRetry6
open R1Z.SimCostWriter R0Z.FsAbort
attribute [local instance] Classical.propDecidable

def scan : (n : Nat) → (Fin n → Costed Bool) → Costed (Option (Fin n))
  | 0, _ => (none,1)
  | n+1, checks =>
    bind (checks 0) fun good =>
      if good then (some 0,2) else
        bind (scan n (fun i => checks i.succ)) fun rest => (rest.map Fin.succ,2)

/-- Least accepted index, or complete rejection, including early exit. -/
theorem scan_spec (n : Nat) (checks : Fin n → Costed Bool) :
    match (scan n checks).1 with
    | none => ∀ i, (checks i).1 = false
    | some k => (checks k).1 = true ∧ ∀ i, i < k → (checks i).1 = false := by
  induction n with
  | zero => intro i; exact Fin.elim0 i
  | succ n ih =>
    simp only [scan, erase_bind]
    cases hb : (checks 0).1 with
    | true =>
      simp only [↓reduceIte]
      exact ⟨hb, fun i hi => False.elim (Fin.not_lt_zero i hi)⟩
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, erase_bind]
      have ht := ih (fun i => checks i.succ)
      cases hh : (scan n (fun i => checks i.succ)).1 with
      | none =>
        simp only [hh, Option.map_none] at ht ⊢
        intro i
        exact Fin.cases hb ht i
      | some k =>
        simp only [hh, Option.map_some] at ht ⊢
        refine ⟨ht.1, ?_⟩
        intro i hi
        refine Fin.cases ?_ (fun j hj => ?_) i hi
        · intro _; exact hb
        · exact ht.2 j (Fin.succ_lt_succ_iff.mp hj)

theorem scan_bound (n C : Nat) (checks : Fin n → Costed Bool)
    (hc : ∀ i, (checks i).2 ≤ C) : (scan n checks).2 ≤ n*(C+2)+1 := by
  induction n with
  | zero => simp only [scan, Nat.zero_mul, Nat.zero_add, le_refl]
  | succ n ih =>
    have h0 := hc 0
    have ht := ih (fun i => checks i.succ) (fun i => hc i.succ)
    simp only [scan, cost_bind]
    split <;> simp only [cost_bind] <;> nlinarith

/-- Exact erasure to the actual firstGood definition, including failure. -/
theorem scan_firstGood {C : Type} (P : C → Prop) (n : Nat) (coins : Fin n → C)
    (check : C → Costed Bool) (he : ∀ c, (check c).1 = true ↔ P c) :
    (scan n (fun i => check (coins i))).1 = firstGood P coins := by
  have hs := scan_spec n (fun i => check (coins i))
  cases hh : (scan n (fun i => check (coins i))).1 with
  | none =>
    rw [hh] at hs
    cases hf : firstGood P coins with
    | none => rfl
    | some k =>
      have hp := (he _).mpr (firstGood_spec P coins k hf)
      rw [hs k] at hp
      cases hp
  | some k =>
    rw [hh] at hs
    cases hf : firstGood P coins with
    | none => exact False.elim ((firstGood_none P coins hf k) ((he _).mp hs.1))
    | some j =>
      have hkj : k ≤ j := by
        by_contra h
        have hp := (he _).mpr (firstGood_spec P coins j hf)
        rw [hs.2 j (by omega)] at hp
        cases hp
      have hjk := firstGood_least P coins j hf k ((he _).mp hs.1)
      exact congrArg some (le_antisymm hkj hjk)

/-- Numeric outer-control overhead: eight exact decisions plus 17 ticks.
The unknown predicate budget C is displayed, not silently discharged. -/
theorem eight_bound (C : Nat) (checks : Fin 8 → Costed Bool)
    (hc : ∀ i, (checks i).2 ≤ C) : (scan 8 checks).2 ≤ 8*C+17 := by
  have h := scan_bound 8 C checks hc
  omega

#print axioms scan_spec
#print axioms scan_bound
#print axioms scan_firstGood
#print axioms eight_bound
end R1Z.SimCostOuterRetry6
