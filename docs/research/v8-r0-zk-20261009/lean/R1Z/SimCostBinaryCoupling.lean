import R1Z.SimCostBinarySource
import R1Z.CouplingR1PBin

/-! Actual binary-word-source coupling to independent uniform residue codes.
The auxiliary uniform fallback exists only on the coupling space: it is not
installed in the truncated implementation, which retains its explicit failure.
The batch failure mass is the previously budgeted extraMass. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.SimCostBinaryCoupling
open R0Z R0Z.FsAbortBounds R1Z.CouplingR1PBin R1Z.SimCostBinarySource
  R1Z.SimCostLazyCoupling R1Z.SimCostTruncationBudget
attribute [local instance] Classical.propDecidable

abbrev Source (m B : Nat) := (Fin B → Fin (m+1)) × Fin m

def complete (m B : Nat) (r : Source m B) : Fin m := (words m B r.1).1.getD r.2

theorem complete_uniform (m : Nat) [NeZero m] (B : Nat) : MP (complete m B) := by
  intro f
  rw [LawTransport.mean_product]
  change mean (fun u : Fin B → Fin (m+1) => mean (fun z : Fin m =>
    f ((words m B u).1.getD z))) = mean f
  rw [mean_swap]
  have inner (z : Fin m) := words_law m B (fun value => f (value.getD z))
  simp only [Option.getD_none, Option.getD_some] at inner
  simp_rw [inner]
  rw [mean_add'']
  have hl : mean (fun z : Fin m => (rejection (Fin m))^B * f z) =
      mean f * (rejection (Fin m))^B := by
    simpa only [mul_comm] using mean_mul_const f ((rejection (Fin m))^B)
  rw [hl, mean_const']
  ring

theorem complete_agrees (m B : Nat) (r : Source m B)
    (h : (words m B r.1).1 ≠ none) :
    (words m B r.1).1 = some (complete m B r) := by
  cases he : (words m B r.1).1 with
  | none => exact False.elim (h he)
  | some v => simp only [complete, he, Option.getD_some]

def batchComplete (m B samples : Nat) (r : Fin samples → Source m B) : Fin samples → Fin m :=
  fun i => complete m B (r i)

theorem batch_uniform (m : Nat) [NeZero m] (B samples : Nat) : MP (batchComplete m B samples) :=
  mp_pi (complete_uniform m B) samples

abbrev M31Source (B : Nat) := Source 2147483647 B

def bad (B samples : Nat) (r : Fin samples → M31Source B) : Prop :=
  ∃ i, (words 2147483647 B (r i).1).1 = none

theorem batch_agrees (B samples : Nat) (r : Fin samples → M31Source B) (h : ¬ bad B samples r) :
    ∀ i, (words 2147483647 B (r i).1).1 = some (batchComplete 2147483647 B samples r i) := by
  intro i
  exact complete_agrees _ _ (r i) (fun hi => h ⟨i,hi⟩)

theorem batch_failure_mass (B samples : Nat) :
    mass (bad B samples) ≤ (samples : ℚ) * (1/(2:ℚ)^(31*B)) := by
  have hi (i : Fin samples) :
      mass (fun r : Fin samples → M31Source B => (words 2147483647 B (r i).1).1 = none) =
        1/(2:ℚ)^(31*B) := by
    let g : M31Source B → ℚ := fun r =>
      @ite ℚ ((words 2147483647 B r.1).1 = none) (Classical.propDecidable _) 1 0
    have he := R0Z.FsAbort.mean_eval i g
    have hp := mp_fst (X := Fin B → Fin 2147483648) (Y := Fin 2147483647)
      (fun u => @ite ℚ ((words 2147483647 B u).1 = none) (Classical.propDecidable _) 1 0)
    have hs : mean (fun u : Fin B → Fin 2147483648 =>
        @ite ℚ ((words 2147483647 B u).1 = none) (Classical.propDecidable _) 1 0) =
        1/(2:ℚ)^(31*B) := by
      convert m31_source_tail B using 1
      apply congrArg mean
      funext u
      by_cases hf : (words 2147483647 B u).1 = none
      · simp only [if_pos hf]
      · simp only [if_neg hf]
    exact he.trans (hp.trans hs)
  have hu := mass_exists_le_card (S := Fin samples → M31Source B) (ι := Fin samples)
    (fun i (r : Fin samples → M31Source B) => (words 2147483647 B (r i).1).1 = none)
    (1/(2:ℚ)^(31*B)) (fun i => (hi i).le)
  unfold bad
  exact hu.trans_eq (by rw [Fintype.card_fin])

theorem eight_failure_budget (samples : Nat) : mass (bad 8 samples) ≤ extraMass samples := by
  have hb := batch_failure_mass 8 samples
  rw [extra_mass_exact]
  change mass (bad 8 samples) ≤ (samples : ℚ) * (1/(2:ℚ)^248) at hb
  exact hb.trans_eq (by ring)

/-- The actual bounded source's fresh-draw cost. This is not the field-stage
arithmetic/metadata cost, and the unused coupling fallback is not drawn by it. -/
theorem batch_draws (B samples : Nat) (r : Fin samples → M31Source B) :
    ∑ i, (words 2147483647 B (r i).1).2 ≤ B*samples := by
  have hh := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => trials_bound B (streamEquiv 2147483647 B (r i).1))
  simpa only [words, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, mul_comm] using hh

/-- Every [0,1]-valued observer can be transported along the actual coupling
at the union truncation cost. Agreement is required only outside failure. -/
theorem observer_transfer (samples : Nat)
    (real : (Fin samples → M31Source 8) → ℚ) (ideal : (Fin samples → Fin 2147483647) → ℚ)
    (hr : ∀ r, 0 ≤ real r ∧ real r ≤ 1)
    (hi : ∀ v, 0 ≤ ideal v ∧ ideal v ≤ 1)
    (ha : ∀ r, ¬ bad 8 samples r → real r = ideal (batchComplete 2147483647 8 samples r)) :
    |mean real - mean ideal| ≤ extraMass samples := by
  have hb := R0Z.FsAbort.until_bad real
    (fun r => ideal (batchComplete 2147483647 8 samples r)) hr
    (fun r => hi _) (bad 8 samples) ha
  rw [batch_uniform 2147483647 8 samples ideal] at hb
  exact hb.trans (eight_failure_budget samples)

/-- The existing numeric privacy envelope plus the ACTUAL source failure
mass stays below 2^-100 once a simulator sample-count bound is supplied. -/
theorem total_source_error (epsilon : ℚ)
    (he : epsilon ≤ 1/(2:ℚ)^109 + 1/(2:ℚ)^137 + 1/(2:ℚ)^454 +
      128*((2:ℚ)^25+1)/(2:ℚ)^190)
    (samples : Nat) (hs : samples ≤ 2^128) :
    epsilon + mass (bad 8 samples) < 1/(2:ℚ)^100 := by
  have hb := eight_failure_budget samples
  have hm : epsilon + mass (bad 8 samples) ≤ epsilon + extraMass samples := by linarith
  exact lt_of_le_of_lt hm (total_below_target epsilon he samples hs)

#print axioms complete_uniform
#print axioms complete_agrees
#print axioms batch_uniform
#print axioms batch_agrees
#print axioms batch_failure_mass
#print axioms eight_failure_budget
#print axioms batch_draws
#print axioms observer_transfer
#print axioms total_source_error
end R1Z.SimCostBinaryCoupling
