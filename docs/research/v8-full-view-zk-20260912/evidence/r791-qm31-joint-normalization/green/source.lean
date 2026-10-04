import AspisV8R19.R789MappedJointNormalization
import AspisV8R15.ExactTowerBase
namespace AspisV8R19.R791QM31JointNormalization
open AspisV8R15.ExactTowerBase
open AspisV8R19.R779FixedPoint1LowKernel
open AspisV8R19.R748JointWitnessPointEntry (z)
open AspisV8R19.R781NormalizedActivePreservation
open AspisV8R19.R746SelectedJointMinor
noncomputable section
set_option autoImplicit false

def witnessEmbedding : M →+* QM31Exact :=
  (algebraMap CM31Exact QM31Exact).comp (algebraMap M31Exact CM31Exact)

local instance : NeZero (2 : QM31Exact) := ⟨by
  intro h
  have hh := congrArg (fun x : QM31Exact => x.re.re) h
  change (2 : M31Exact) = 0 at hh
  exact (by decide : (2 : M31Exact) ≠ 0) hh⟩

theorem qm31_normalized_matrix (t : Fin 22 → QM31Exact)
    (ht : Function.Injective t) (noneOne : ∀ i, t i ≠ 1) :
    normalizedSelectedMatrix (witnessEmbedding half)
      (witnessEmbedding (536870912 : M)) 7 2 3 5 0
      (fun i => witnessEmbedding (z i)) t ht noneOne =
    chosenSourceMatrix (witnessEmbedding half)
      (witnessEmbedding (536870912 : M)) 7 2 3 5 0
      (fun i => witnessEmbedding (z i)) :=
  R789MappedJointNormalization.mapped_normalized_matrix witnessEmbedding t ht noneOne

#print axioms witnessEmbedding
#print axioms qm31_normalized_matrix
end
end AspisV8R19.R791QM31JointNormalization
