import AspisV8R19.OODDistinctRetryLaw
import AspisV8R19.SamplerCirclePolicy

/-! Ideal three-attempt secure-OOD parameter wrapper.  Each attempt is a
uniform exact QM31 value and succeeds precisely when its imaginary CM31
component is nonzero.  This is the value-level law used after, not instead of,
the source byte-sampler correspondence. -/
set_option autoImplicit false
namespace AspisV8R19.OODParameterRetryLaw
open AspisV8R15.ExactTowerBase
open AspisV8R15.ExactTowerChord
open AspisR19.TwoSwapSourceDomains
open AspisR19.TwoSwapFixedRootProbability
open AspisV8R17.BoundedRejection
open AspisV8Privacy
noncomputable section

local instance : DecidableEq QM31Exact := Classical.decEq _
local instance cm31Fintype : Fintype CM31Exact :=
  Fintype.ofEquiv (M31Exact × M31Exact)
    (QuadraticAlgebra.equivProd (-1 : M31Exact) 0).symm
local instance qm31Fintype : Fintype QM31Exact :=
  Fintype.ofEquiv (CM31Exact × CM31Exact)
    (QuadraticAlgebra.equivProd qm31R 0).symm
local instance : Nonempty QM31Exact := ⟨0⟩

def accept (z : QM31Exact) : Bool := decide (z.im ≠ 0)

theorem rejected_domain_card :
    Fintype.card {z : QM31Exact // accept z = false} = P ^ 2 := by
  calc
    Fintype.card {z : QM31Exact // accept z = false} =
        Fintype.card {z : QM31Exact // z.im = 0} := by
      apply Fintype.card_congr
      exact Equiv.subtypeEquivRight (by simp [accept])
    _ = P ^ 2 := imZero_card

theorem full_domain_card : Fintype.card QM31Exact = P ^ 4 := qm31_card

theorem failure_probability :
    uniformProbability (@sample QM31Exact accept 3) none =
      ((P ^ 2 : Nat) : ℚ) ^ 3 / (((P ^ 4 : Nat) : ℚ) ^ 3) := by
  rw [AspisV8R17.BoundedRejection.failure_probability]
  rw [rejected_domain_card, full_domain_card]

theorem accepted_output_probabilities_equal (v w : QM31Exact)
    (hv : v.im ≠ 0) (hw : w.im ≠ 0) :
    uniformProbability (@sample QM31Exact accept 3) (some v) =
      uniformProbability (@sample QM31Exact accept 3) (some w) := by
  apply accepted_probabilities_equal accept 3 v w
  · simpa only [accept, decide_eq_true_eq] using hv
  · simpa only [accept, decide_eq_true_eq] using hw

theorem pureMap_success_iff (t : QM31Exact) :
    (SamplerCirclePolicy.pureMap t).toOption.isSome ↔ t.im ≠ 0 := by
  constructor
  · intro h
    cases hp : SamplerCirclePolicy.pureMap t with
    | error e =>
        rw [hp] at h
        simp only [Except.toOption, Option.isSome, Bool.false_eq_true] at h
    | ok p => exact (SamplerCirclePolicy.success_policy t p hp).1
  · intro h
    rw [SamplerCirclePolicy.outside_map t h]
    rfl

theorem source_accept_iff (xs : List Nat) :
    (SamplerCirclePolicy.accept xs).isSome ↔
      accept (SamplerFieldDecode.decode xs) = true := by
  rw [show SamplerCirclePolicy.accept xs =
      (SamplerCirclePolicy.pureMap (SamplerFieldDecode.decode xs)).toOption by rfl,
    pureMap_success_iff]
  simp only [accept, decide_eq_true_eq]

#print axioms rejected_domain_card
#print axioms full_domain_card
#print axioms failure_probability
#print axioms accepted_output_probabilities_equal
#print axioms pureMap_success_iff
#print axioms source_accept_iff
end
end AspisV8R19.OODParameterRetryLaw
