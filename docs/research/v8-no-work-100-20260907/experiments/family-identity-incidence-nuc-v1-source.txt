import SupportQualifiedRootIncidence

/-! Additive identity-incidence accounting across a finite family.
Each challenge set may overlap every other one. We weaken each identity
count to one common threshold, sum the weights, and bound the union.
There is no multiplier by the number of factors and no numerical field
enumeration. A polynomial corollary derives the individual incidences from
the already checked maximal root-support sets.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 150000
set_option maxRecDepth 200

namespace AspisV8.FamilyIdentityIncidence
open Finset Polynomial

/-- Cross-multiplied monotonicity of `(T-b)/(a-b)`. The domain condition
`a <= T` is necessary for this direction of weakening. -/
theorem ratio_monotone (T a b bbar : Nat) (domain : a ≤ T)
    (small : b ≤ bbar) (threshold : bbar ≤ a) :
    (T-b)*(a-bbar) ≤ (T-bbar)*(a-b) := by
  have top : T-b = (T-bbar)+(bbar-b) := by omega
  have bottom : a-b = (a-bbar)+(bbar-b) := by omega
  have height : a-bbar ≤ T-bbar := Nat.sub_le_sub_right domain bbar
  rw [top, bottom, Nat.add_mul, Nat.mul_add]
  apply Nat.add_le_add_left
  simpa only [Nat.mul_comm] using Nat.mul_le_mul_right (bbar-b) height

/-- An individual adaptive-support bound can use the common larger identity
threshold without changing its own weight. -/
theorem common_threshold (n w T a b bbar : Nat) (domain : a ≤ T)
    (small : b ≤ bbar) (threshold : bbar < a)
    (incidence : n*(a-b) ≤ w*(T-b)) :
    n*(a-bbar) ≤ w*(T-bbar) := by
  have cross := ratio_monotone T a b bbar domain small threshold.le
  have positive : 0 < a-b := by omega
  apply Nat.le_of_mul_le_mul_right (c := a-b) ?_ positive
  calc
    (n*(a-bbar))*(a-b) = (n*(a-b))*(a-bbar) := by ac_rfl
    _ ≤ (w*(T-b))*(a-bbar) := Nat.mul_le_mul_right (a-bbar) incidence
    _ = w*((T-b)*(a-bbar)) := by ac_rfl
    _ ≤ w*((T-bbar)*(a-b)) := Nat.mul_le_mul_left w cross
    _ = (w*(T-bbar))*(a-b) := by ac_rfl

/-- Union the challenge sets, not their cardinality estimates multiplied by
the number of factors. Neither disjointness nor nonempty factors is needed. -/
theorem family_union_bound {I J : Type*} [DecidableEq J]
    (F : Finset I) (G : I → Finset J) (b weight : I → Nat)
    (T a bbar W : Nat) (domain : a ≤ T) (threshold : bbar < a)
    (identities : ∀ f ∈ F, b f ≤ bbar)
    (incidence : ∀ f ∈ F, (G f).card*(a-b f) ≤ weight f*(T-b f))
    (budget : (∑ f ∈ F, weight f) ≤ W) :
    (F.biUnion G).card*(a-bbar) ≤ W*(T-bbar) := by
  have rows := Finset.sum_le_sum (fun f hf =>
    common_threshold (G f).card (weight f) T a (b f) bbar
      domain (identities f hf) threshold (incidence f hf))
  simp only [← Finset.sum_mul] at rows
  calc
    _ ≤ (∑ f ∈ F, (G f).card)*(a-bbar) :=
      Nat.mul_le_mul_right (a-bbar) (Finset.card_biUnion_le)
    _ ≤ (∑ f ∈ F, weight f)*(T-bbar) := rows
    _ ≤ _ := Nat.mul_le_mul_right (T-bbar) budget

/-- Fixed coordinate polynomials give the individual bounds, rather than
requiring them as an unexplained factor-family premise. These maximal
support sets capture arbitrary gamma-adaptive matching candidates. -/
theorem polynomial_family_bound {I J K : Type*} [DecidableEq I]
    [Field K] [DecidableEq K] (D : Finset I) (F : Finset J)
    (Gamma : Finset K) (E : J → I → K[X]) (weight : J → Nat)
    (a bbar W : Nat) (domain : a ≤ D.card) (threshold : bbar < a)
    (degree : ∀ f ∈ F, ∀ i ∈ D, (E f i).natDegree ≤ weight f)
    (identities : ∀ f ∈ F,
      (SupportQualifiedRootIncidence.identityCoordinates D (E f)).card ≤ bbar)
    (budget : (∑ f ∈ F, weight f) ≤ W) :
    (F.biUnion fun f =>
      SupportQualifiedRootIncidence.qualifyingGammas D Gamma (E f) a).card *
        (a-bbar) ≤ W*(D.card-bbar) := by
  apply family_union_bound F
    (fun f => SupportQualifiedRootIncidence.qualifyingGammas D Gamma (E f) a)
    (fun f => (SupportQualifiedRootIncidence.identityCoordinates D (E f)).card)
    weight D.card a bbar W domain threshold identities
  · intro f hf
    exact SupportQualifiedRootIncidence.qualifying_gammas_bound D Gamma (E f)
      a (weight f) (degree f hf)
  · exact budget

#print axioms ratio_monotone
#print axioms common_threshold
#print axioms family_union_bound
#print axioms polynomial_family_bound
end AspisV8.FamilyIdentityIncidence
