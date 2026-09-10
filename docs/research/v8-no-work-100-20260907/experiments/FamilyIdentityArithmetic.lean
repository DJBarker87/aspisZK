import FamilyIdentityIncidence
import AspisFormal.V5ComponentCQM31TowerExact

/-! A separate closed-arithmetic specialization of additive family incidence.
The only large integer expressions are the proven field cardinality P^4
and 2^100. `norm_num` certifies these fixed powers by arithmetic; no QM31
elements, Fin enumerations or generated recurrence cells are reduced.
This is an integer budget, not a theorem about actual sampler freshness.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 100000
set_option maxRecDepth 200

namespace AspisV8.FamilyIdentityArithmetic
open Finset
open AspisV5ComponentCQM31TowerExact

theorem selected_numbers :
    38230-31129=7101 ∧
      117077*(1048576-31129)=119119642419 ∧
      119119642419/7101=16775051 := by
  norm_num

/-- Exact selected union cap, independent of the number or overlap of
factors. The per-factor incidences and identity cap remain explicit. -/
theorem family_card_le {I J : Type*} [DecidableEq J]
    (F : Finset I) (G : I → Finset J) (b weight : I → Nat)
    (identities : ∀ f ∈ F, b f ≤ 31129)
    (incidence : ∀ f ∈ F,
      (G f).card*(38230-b f) ≤ weight f*(1048576-b f))
    (budget : (∑ f ∈ F, weight f) ≤ 117077) :
    (F.biUnion G).card ≤ 16775051 := by
  have bound := FamilyIdentityIncidence.family_union_bound F G b weight
    1048576 38230 31129 117077 (by norm_num) (by norm_num)
    identities incidence budget
  rw [selected_numbers.1, selected_numbers.2.1] at bound
  omega

/-- Reuse the actual tower's cardinality theorem before doing closed Nat
arithmetic. This does not synthesize a field enumeration. -/
theorem qm31_nonzero_budget :
    (Fintype.card QM31Exact-1)/2^100=16777215 := by
  rw [qm31Exact_card]
  norm_num [P]

theorem selected_cap_le_budget :
    16775051 ≤ (Fintype.card QM31Exact-1)/2^100 := by
  rw [qm31_nonzero_budget]
  norm_num

/-- The integer form of a100-raw-bit ceiling for any count within the
selected cap. A probability interpretation still needs uniform nonzero
gamma; it is not supplied by this arithmetic corollary. -/
theorem bounded_count_100_bits (n : Nat) (bound : n ≤ 16775051) :
    n*2^100 ≤ Fintype.card QM31Exact-1 := by
  exact (Nat.le_div_iff_mul_le (by positivity : 0 < (2 : Nat)^100)).mp
    (bound.trans selected_cap_le_budget)

#print axioms selected_numbers
#print axioms family_card_le
#print axioms qm31_nonzero_budget
#print axioms selected_cap_le_budget
#print axioms bounded_count_100_bits
end AspisV8.FamilyIdentityArithmetic
