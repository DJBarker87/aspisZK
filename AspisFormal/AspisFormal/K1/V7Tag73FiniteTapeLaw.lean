import AspisFormal.K1.V7Tag73AdaptiveLazyOracle
import AspisFormal.K1.V7Tag73FiniteSubkernel

/-!
# Exact finite-tape law, with bind rather than an assumed experiment law

The uniform-product identity is proved for an abstract finite alphabet BEFORE
specializing to 256-bit digests. No concrete tape enumeration is reduced.
-/
set_option autoImplicit false
namespace AspisK1.V7Tag73FiniteTapeLaw
open MeasureTheory
open scoped BigOperators
open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73FiniteSubkernel
noncomputable section
variable {A : Type} [Fintype A] [Nonempty A]

/-- An independent tape of raw answers; abort is an event, not a renormalization. -/
def iidTape (law : PMF A) : (n : Nat) → PMF (FreshAnswerTape A n)
  | 0 => PMF.pure PUnit.unit
  | n + 1 => law.bind fun a => (iidTape law n).map fun tail => (a, tail)

/-- One-step disintegration on the explicitly constructed law. -/
theorem iidTape_event_succ (law : PMF A) (n : Nat)
    (event : Set (FreshAnswerTape A (n + 1))) :
    (iidTape law (n + 1)).toOuterMeasure event =
      ∑ a, law a * (iidTape law n).toOuterMeasure
        {tail | (a, tail) ∈ event} := by
  unfold iidTape
  rw [PMF.toOuterMeasure_bind_apply]
  simp only [PMF.toOuterMeasure_map_apply, tsum_fintype]
  rfl

private theorem finite_natCast_mul_inv (m n : Nat) :
    (((m : ENNReal) * (n : ENNReal))⁻¹) =
      (m : ENNReal)⁻¹ * (n : ENNReal)⁻¹ := by
  apply ENNReal.mul_inv
  · exact Or.inr (by simp)
  · exact Or.inl (by simp)

/-- Extensional proof: the nested independent uniform law is the repository's
uniform law on the full product type. No source-law premise occurs here. -/
theorem iidTape_uniform (n : Nat) :
    iidTape (PMF.uniformOfFintype A) n =
      PMF.uniformOfFintype (FreshAnswerTape A n) := by
  classical
  induction n with
  | zero =>
      ext t
      cases t
      simp [iidTape, FreshAnswerTape, PMF.uniformOfFintype_apply]
  | succ n ih =>
      ext t
      rcases t with ⟨a, tail⟩
      simp [iidTape, PMF.bind_apply, PMF.map_apply, ih,
        PMF.uniformOfFintype_apply, FreshAnswerTape, Fintype.card_prod,
        finite_natCast_mul_inv, mul_comm, mul_left_comm, mul_assoc]

/-- A head-only event ignores every later coordinate, not just successful tails. -/
theorem iidTape_head_event (law : PMF A) (n : Nat) (event : Set A) :
    (iidTape law (n + 1)).toOuterMeasure {t | t.1 ∈ event} =
      law.toOuterMeasure event := by
  unfold iidTape
  rw [PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_apply]
  apply tsum_congr
  intro a
  rw [PMF.toOuterMeasure_map_apply]
  by_cases present : a ∈ event <;> simp [present, Set.indicator_apply]

/-- Uniform set mass is the literal finite cardinality fraction. -/
theorem uniform_finset_mass [DecidableEq A] (target : Finset A) :
    (PMF.uniformOfFintype A).toOuterMeasure (target : Set A) =
      (target.card : ENNReal) / (Fintype.card A : ENNReal) := by
  rw [PMF.toOuterMeasure_uniformOfFintype_apply]
  simp

/-- The exact finite-sum subkernel representation of a PMF event. -/
theorem pmf_event_eq_eventMass (law : PMF A) (event : Set A) :
    law.toOuterMeasure event = eventMass law (fun a => a ∈ event) := by
  classical
  simp [PMF.toOuterMeasure_apply, eventMass, tsum_fintype, Set.indicator_apply]

/-- Both endpoints use the same literal digest tape type and uniform PMF. -/
theorem digest_iid_eq_repository (n : Nat) :
    iidTape (PMF.uniformOfFintype
      AspisK1.V7Tag73TranscriptSchedule.Digest256) n =
      uniformDigestFreshTape n := by
  exact iidTape_uniform n

#print axioms iidTape_event_succ
#print axioms iidTape_uniform
#print axioms iidTape_head_event
#print axioms pmf_event_eq_eventMass
#print axioms digest_iid_eq_repository
end
end AspisK1.V7Tag73FiniteTapeLaw
