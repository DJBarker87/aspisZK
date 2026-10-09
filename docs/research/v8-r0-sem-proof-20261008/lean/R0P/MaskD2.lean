import R0P.MaskProtocol
import R0C.Counting

/-! G24: the one-root eta event. Uniform wide-field density and the
embedded-QM31 sampler density have different denominators. -/
set_option autoImplicit false
namespace R0P.Mask
open FS R0P.SemSource R0P.SemD3Glue
open AspisV8R19.OracleResampling AspisV8R19.CausalFirstHitUnionBound
open AspisV8R19.SourceDuplexStep AspisWideTower
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

/-- M = maskTotal; S = originalTotal, both fixed before eta is sampled. -/
def etaBad {K : Type} [Field K] (claim M S eta : K) : Prop :=
  S ≠ 0 ∧ claim = M + eta * S

section Generic
variable {K : Type} [Field K]

theorem etaBad_root {claim M S eta : K} (h : etaBad claim M S eta) :
    eta = (claim - M) / S := by
  apply (eq_div_iff h.1).mpr
  linear_combination -h.2

/-- An arbitrary sampler needs only its atom bound. No degree or other
property of the mask polynomial enters this one-root argument. -/
theorem etaBad_mass_of_atoms {A : Type} [Fintype A]
    (sample : A → K) (q : ℚ) (hq : 0 ≤ q)
    (hAtoms : ∀ y, mean (fun a => indicator (sample a = y)) ≤ q)
    (claim M S : K) : mean (fun a => indicator (etaBad claim M S (sample a))) ≤ q := by
  by_cases hs : S = 0
  · have hfalse (a : A) : etaBad claim M S (sample a) ↔ False :=
      iff_false_intro (fun h => h.1 hs)
    rw [mean_congr (fun a => indicator_iff (hfalse a)), indicator_false]
    simpa only [mean, Finset.sum_const_zero, zero_div] using hq
  · apply le_trans _ (hAtoms ((claim - M) / S))
    apply mean_mono
    intro a
    exact indicator_mono etaBad_root

omit [Field K] in
/-- Symbolic uniform point mass on an abstract finite type. -/
theorem uniform_point_mass [Fintype K] (y : K) :
    mean (fun eta : K => indicator (eta = y)) = 1 / (Fintype.card K : ℚ) := by
  simp [mean, indicator]

theorem etaBad_uniform_mass [Fintype K] (claim M S : K) :
    mean (fun eta : K => indicator (etaBad claim M S eta)) ≤
      1 / (Fintype.card K : ℚ) :=
  etaBad_mass_of_atoms id _ (div_nonneg zero_le_one (Nat.cast_nonneg _))
    (fun y => (uniform_point_mass y).le) claim M S

theorem etaBad_card [Fintype K] (claim M S : K) :
    (Finset.univ.filter (etaBad claim M S)).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro a ha b hb
  exact (etaBad_root (Finset.mem_filter.mp ha).2).trans
    (etaBad_root (Finset.mem_filter.mp hb).2).symm
end Generic

/-- The actual semantic sampler ranges over embedded QM31. Its denominator
is P^4, as in SemD2.semChal_mass (208-223), not card SemE = P^8. -/
theorem etaBad_semChal_mass (claim M S : SemE) :
    mean (fun s : State => indicator (etaBad claim M S (semChal s))) ≤
      (1 + deltaQ) / (AspisCircleGroupOrder.P : ℚ)^4 :=
  etaBad_mass_of_atoms semChal _
    (div_nonneg (add_nonneg zero_le_one deltaQ_nonneg)
      (pow_nonneg (Nat.cast_nonneg _) _)) semChal_mass claim M S

#print axioms etaBad
#print axioms etaBad_root
#print axioms etaBad_mass_of_atoms
#print axioms uniform_point_mass
#print axioms etaBad_uniform_mass
#print axioms etaBad_card
#print axioms etaBad_semChal_mass

/-- The trace is selected by the opening proof from the committed-word list;
an eta event at the earlier prefix must cover every such candidate. -/
def etaSomeBad {K T : Type} [Field K] (ts : Finset T) (total : T → K)
    (claim M eta : K) : Prop := ∃ t ∈ ts, etaBad claim M (total t) eta

theorem etaSomeBad_card {K T : Type} [Field K] [Fintype K]
    (ts : Finset T) (total : T → K) (claim M : K) :
    (Finset.univ.filter (etaSomeBad ts total claim M)).card ≤ ts.card := by
  classical
  let per : T → Finset K := fun t => Finset.univ.filter (etaBad claim M (total t))
  have hsub : Finset.univ.filter (etaSomeBad ts total claim M) ⊆ ts.biUnion per := by
    intro eta he
    obtain ⟨t, ht, hb⟩ := (Finset.mem_filter.mp he).2
    exact Finset.mem_biUnion.mpr ⟨t, ht, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩⟩
  calc
    _ ≤ (ts.biUnion per).card := Finset.card_le_card hsub
    _ ≤ ∑ t ∈ ts, (per t).card := Finset.card_biUnion_le
    _ ≤ ∑ _t ∈ ts, 1 := Finset.sum_le_sum (fun t _ => etaBad_card claim M (total t))
    _ = ts.card := by simp

theorem etaSomeBad_semChal_mass {T : Type} (ts : Finset T) (total : T → SemE)
    (claim M : SemE) :
    mean (fun s : State => indicator (etaSomeBad ts total claim M (semChal s))) ≤
      ts.card * ((1 + deltaQ) / (AspisCircleGroupOrder.P : ℚ)^4) := by
  let bad : Finset SemE := Finset.univ.filter (etaSomeBad ts total claim M)
  have hmem (s : State) : etaSomeBad ts total claim M (semChal s) ↔ semChal s ∈ bad := by
    simp only [bad, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [mean_congr (fun s => indicator_iff (hmem s))]
  apply (semChal_event bad).trans
  apply mul_le_mul_of_nonneg_right
  · exact_mod_cast etaSomeBad_card ts total claim M
  · exact div_nonneg (add_nonneg zero_le_one deltaQ_nonneg)
      (pow_nonneg (Nat.cast_nonneg _) _)

/-- Two possible original sums can give different roots for one claim and
one mask sum. Thus the fixed-trace one-root result is not a union bound. -/
theorem etaBad_two_roots {K : Type} [Field K] [NeZero (2 : K)] :
    (2 : K) ≠ 1 ∧ etaBad (2 : K) 0 1 2 ∧ etaBad (2 : K) 0 2 1 := by
  refine ⟨?_, ⟨one_ne_zero, ?_⟩, ⟨NeZero.ne 2, ?_⟩⟩
  · intro h
    apply one_ne_zero (α := K)
    linear_combination h
  · ring
  · ring

#print axioms etaSomeBad_card
#print axioms etaSomeBad_semChal_mass
#print axioms etaBad_two_roots
end
end R0P.Mask
