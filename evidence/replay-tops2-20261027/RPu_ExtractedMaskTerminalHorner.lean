import RPu_TerminalHornerCore

/-!
Pure adapter for the generated two reverse-Horner folds.  This is only the
finite-field fold algebra; it does not assert that generated arrays equal the
R0P poseidon/semantic/copy lane sources.
-/
set_option autoImplicit false

namespace AspisR1.ExtractedMaskTerminalHorner
open scoped BigOperators

variable {K : Type} [Field K]

def seededHorner (theta seed : K) (cs : List K) : K :=
  cs.reverse.foldl (fun out c => out * theta + c) seed

theorem seededHorner_eq_source (theta seed : K) (cs : List K) :
    seededHorner theta seed cs =
      seed * theta ^ cs.length + AspisR1.TerminalHornerCore.sourceMixHorner theta cs := by
  induction cs with
  | nil => simp [seededHorner, AspisR1.TerminalHornerCore.sourceMixHorner]
  | cons c cs ih =>
      have hstep : seededHorner theta seed (c :: cs) =
          seededHorner theta seed cs * theta + c := by
        simp [seededHorner, List.reverse_cons, List.foldl_append]
      rw [hstep, ih, AspisR1.TerminalHornerCore.sourceMixHorner_cons,
        List.length_cons, pow_succ]
      ring

theorem seededHorner_eq_sum (n : Nat) (cs : Fin n → K) (theta seed : K) :
    seededHorner theta seed (List.ofFn cs) =
      seed * theta ^ n + ∑ i, cs i * theta ^ i.val := by
  rw [seededHorner_eq_source, List.length_ofFn,
    AspisR1.TerminalHornerCore.sourceMixHorner_eq_sum]

/-- Exact model for loop0 then loop1: source order is 24 semantic entries,
then four poseidon entries, with the copy residual as the initial seed. -/
def composeGroups (theta seed : K) (semantic : Fin 24 → K)
    (poseidon : Fin 4 → K) : K :=
  seededHorner theta (seededHorner theta seed (List.ofFn semantic))
    (List.ofFn poseidon)

theorem composeGroups_eq (theta seed : K) (semantic : Fin 24 → K)
    (poseidon : Fin 4 → K) :
    composeGroups theta seed semantic poseidon =
      seed * theta ^ 28 +
        (∑ i : Fin 24, semantic i * theta ^ (i.val + 4)) +
        (∑ j : Fin 4, poseidon j * theta ^ j.val) := by
  rw [composeGroups, seededHorner_eq_sum, seededHorner_eq_sum]
  have hshift :
      (∑ i : Fin 24, semantic i * theta ^ i.val) * theta ^ 4 =
        ∑ i : Fin 24, semantic i * theta ^ (i.val + 4) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [pow_add]
    ring
  rw [add_mul, hshift]
  have hpower : theta ^ 24 * theta ^ 4 = theta ^ 28 := by
    rw [← pow_add]
  rw [mul_assoc, hpower]

/-- Recombine the source fold groups into the 29 coefficients used by the
terminal model. The hypotheses expose, rather than assume away, the separate
array-to-lane source obligations. -/
theorem composeGroups_eq_lane_sum (theta seed : K)
    (semantic : Fin 24 → K) (poseidon : Fin 4 → K) (lanes : Fin 29 → K)
    (hposeidon : ∀ i : Fin 4, poseidon i = lanes (Fin.castAdd 25 i))
    (hsemantic : ∀ i : Fin 24,
      semantic i = lanes (Fin.natAdd 4 (Fin.castAdd 1 i)))
    (hcopy : seed = lanes 28) :
    composeGroups theta seed semantic poseidon =
      ∑ i : Fin 29, theta ^ i.val * lanes i := by
  have hsplit : (∑ i : Fin 29, theta ^ i.val * lanes i) =
      (∑ i : Fin 4, theta ^ i.val * poseidon i) +
        ((∑ i : Fin 24, theta ^ (4 + i.val) * semantic i) +
          theta ^ 28 * seed) := by
    rw [Fin.sum_univ_add (a := 4) (b := 25)]
    congr 1
    · apply Finset.sum_congr rfl
      intro i hi
      rw [hposeidon]
      rfl
    · rw [Fin.sum_univ_add (a := 24) (b := 1)]
      congr 1
      · apply Finset.sum_congr rfl
        intro i hi
        rw [hsemantic]
        rfl
      · rw [Fin.sum_univ_one]
        rw [hcopy]
        rfl
  rw [hsplit, composeGroups_eq]
  have hsemantic_sum :
      (∑ i : Fin 24, semantic i * theta ^ (i.val + 4)) =
        ∑ i : Fin 24, theta ^ (4 + i.val) * semantic i := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [Nat.add_comm i.val 4, mul_comm]
  have hposeidon_sum :
      (∑ i : Fin 4, poseidon i * theta ^ i.val) =
        ∑ i : Fin 4, theta ^ i.val * poseidon i := by
    apply Finset.sum_congr rfl
    intro i hi
    exact mul_comm _ _
  rw [hsemantic_sum, hposeidon_sum]
  ring

#print axioms seededHorner_eq_source
#print axioms seededHorner_eq_sum
#print axioms composeGroups_eq
#print axioms composeGroups_eq_lane_sum

end AspisR1.ExtractedMaskTerminalHorner
