import AspisFormal.K1.V7Tag73JointQueryBatchSoundness
import AspisFormal.K1.V7Tag73FiniteSubkernel
import AspisFormal.K1.V7Tag73StoppedSamplerKernel
import AspisFormal.K1.V7Tag73RetrySamplerTapeReflection

/-!
# Degree-sixteen joint batch target on a pre-answer checkpoint

This reuses the repository's real shifted-query polynomial and its root bound.
There is no replacement polynomial and no work normalization. Raw decoder atom
bounds and source/checkpoint reflection are separate obligations.
-/
set_option autoImplicit false
namespace AspisK1.V7Tag73RestoredJointBatchKernel
open scoped BigOperators
open AspisK1.V7Tag73JointQueryBatchSoundness
open AspisK1.V7Tag73FiniteSubkernel
open AspisK1.V7Tag73StoppedSamplerKernel
open AspisK1.V7Tag73RetrySamplerTapeReflection
open AspisK1.V7Tag73FiniteTapeLaw
open AspisV6QueryBatchSoundness
noncomputable section
variable {K Raw : Type*} [Field K] [Fintype K] [DecidableEq K] [Fintype Raw]

/-- Exactly the data that must be fixed before the NEW restored rho draw. -/
structure BatchCheckpoint (K : Type*) where
  priorDiscrepancy : K
  expected : Fin 16 → K
  authenticated : Fin 16 → K

def BatchCheckpoint.target (s : BatchCheckpoint K) : Finset K :=
  jointQueryBatchNonzeroCollisionSet s.priorDiscrepancy s.expected s.authenticated

theorem checkpoint_target_card (s : BatchCheckpoint K)
    (different : s.expected ≠ s.authenticated) : s.target.card ≤ 16 :=
  jointQueryBatch_nonzero_collision_card_le_sixteen_of_vectors_ne
    s.priorDiscrepancy s.expected s.authenticated different

/-- Pointwise source equalities turn a concrete zero discrepancy into target
membership. The challenge is NOT included among the checkpoint fields. -/
theorem zero_discrepancy_mem_checkpoint (s : BatchCheckpoint K) (rho : K)
    (nonzero : rho ≠ 0)
    (zero : jointQueryBatchDiscrepancy s.priorDiscrepancy s.expected
      s.authenticated rho = 0) : rho ∈ s.target :=
  mem_jointQueryBatchNonzeroCollisionSet_of_nonzero_of_zero
    s.priorDiscrepancy s.expected s.authenticated rho nonzero zero

/-- Exact raw-kernel collision bound. No assumption that accepted executions
are uniformly distributed is used. -/
theorem checkpoint_decoded_collision_mass_le
    (w : Raw → ENNReal) (decode : Raw → Option K) (s : BatchCheckpoint K)
    (different : s.expected ≠ s.authenticated) (atomCap : ENNReal)
    (atomBound : ∀ value ∈ s.target, decodedAtomMass w decode value ≤ atomCap) :
    eventMass w (fun raw => ∃ value ∈ s.target, decode raw = some value) ≤
      16 * atomCap := by
  exact (decoded_bad_mass_le w decode s.target atomCap atomBound).trans
    (mul_le_mul_right' (by exact_mod_cast checkpoint_target_card s different) atomCap)

/-- Subsequent acceptance may depend on rho and all later answers. Filtering
cannot INCREASE this unnormalised collision mass. Rejection is not erased
from the separate extraction-failure analysis. -/
theorem accepted_checkpoint_collision_mass_le
    (w : Raw → ENNReal) (decode : Raw → Option K) (s : BatchCheckpoint K)
    (different : s.expected ≠ s.authenticated) (atomCap : ENNReal)
    (atomBound : ∀ value ∈ s.target, decodedAtomMass w decode value ≤ atomCap)
    (accept : Raw → Prop) :
    eventMass w (fun raw => accept raw ∧
      ∃ value ∈ s.target, decode raw = some value) ≤ 16 * atomCap :=
  (accepted_bad_mass_le w accept _).trans
    (checkpoint_decoded_collision_mass_le w decode s different atomCap atomBound)

/-- Full bounded-retry target charge. Do not replace geometricWeight by one
unless the actual sampler law justifies that sharper statement. -/
theorem checkpoint_retry_collision_mass_le
    (w : Raw → ENNReal) (decode : Raw → Option K) (s : BatchCheckpoint K)
    (different : s.expected ≠ s.authenticated) (atomCap : ENNReal)
    (atomBound : ∀ value ∈ s.target, decodedAtomMass w decode value ≤ atomCap)
    (n : Nat) :
    (∑ value ∈ s.target, firstSuccessAtom w decode value n) ≤
      16 * atomCap * geometricWeight (rejectMass w decode) n := by
  calc
    (∑ value ∈ s.target, firstSuccessAtom w decode value n) =
        (∑ value ∈ s.target, decodedAtomMass w decode value) *
          geometricWeight (rejectMass w decode) n := by
      simp only [firstSuccessAtom_factor, Finset.sum_mul]
    _ ≤ ((s.target.card : ENNReal) * atomCap) *
        geometricWeight (rejectMass w decode) n := by
      apply mul_le_mul_right'
      calc
        (∑ value ∈ s.target, decodedAtomMass w decode value) ≤
            ∑ _value ∈ s.target, atomCap := Finset.sum_le_sum atomBound
        _ = (s.target.card : ENNReal) * atomCap := by simp [nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_right'
      (mul_le_mul_right' (by exact_mod_cast checkpoint_target_card s different) atomCap) _

/-- The bounded-retry collision bound for the actual generic tape sampler.
Production use additionally requires the real sampler-to-firstDecoded theorem. -/
theorem checkpoint_retry_tape_probability_le
    {Raw0 : Type} [Fintype Raw0] [Nonempty Raw0]
    (law : PMF Raw0) (decode : Raw0 → Option K) (s : BatchCheckpoint K)
    (different : s.expected ≠ s.authenticated) (atomCap : ENNReal)
    (atomBound : ∀ value ∈ s.target, decodedAtomMass law decode value ≤ atomCap)
    (n : Nat) :
    (iidTape law n).toOuterMeasure
      {t | ∃ value ∈ s.target, firstDecoded decode n t = some value} ≤
      16 * atomCap * geometricWeight (rejectMass law decode) n := by
  exact (firstDecoded_target_mass_le law decode s.target atomCap atomBound n).trans
    (mul_le_mul_right'
      (mul_le_mul_right' (by exact_mod_cast checkpoint_target_card s different) atomCap) _)

#print axioms checkpoint_retry_tape_probability_le

#print axioms checkpoint_target_card
#print axioms zero_discrepancy_mem_checkpoint
#print axioms checkpoint_decoded_collision_mass_le
#print axioms accepted_checkpoint_collision_mass_le
#print axioms checkpoint_retry_collision_mass_le
end
end AspisK1.V7Tag73RestoredJointBatchKernel
