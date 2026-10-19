import R0.Dot
import Wide.InitialEncoder

set_option autoImplicit false
namespace AspisR0.Opening
open AspisPool.AlgorithmicCircleDecoderV7
open AspisWide.InitialEncoder
open AspisR0.RoundNormalization
open scoped BigOperators
noncomputable section
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K]

/-- The Boolean multilinear equality weights, indexed by the ten bits. -/
def eqWeight (p : Fin 10 → K) : InitialMessage K := fun r =>
  ∏ b : Fin 10, if r.val / 2^b.val % 2 = 0 then 1-p b else p b

def indicator (I : Finset (Fin 1024)) : InitialMessage K := fun r => if r ∈ I then 1 else 0

/-- A row-space weight reindexed into coefficient space. -/
def coeffWeight (π : Fin 1024 ≃ Fin 1024) (w : InitialMessage K) : InitialMessage K :=
  fun j => w (π.symm j)

theorem coeffWeight_add (π : Fin 1024 ≃ Fin 1024) (w v : InitialMessage K) :
    coeffWeight π (w + v) = coeffWeight π w + coeffWeight π v := rfl

theorem coeffWeight_smul (π : Fin 1024 ≃ Fin 1024) (a : K) (w : InitialMessage K) :
    coeffWeight π (a • w) = a • coeffWeight π w := rfl

theorem coeffWeight_sum {ι : Type*} (π : Fin 1024 ≃ Fin 1024)
    (s : Finset ι) (w : ι → InitialMessage K) :
    coeffWeight π (∑ i ∈ s, w i) = ∑ i ∈ s, coeffWeight π (w i) := by
  funext j
  simp only [coeffWeight, Finset.sum_apply]

theorem dot_coeffWeight_left (π : Fin 1024 ≃ Fin 1024) (w m : InitialMessage K) :
    dot (coeffWeight π w) m = dot w (fun r => m (π r)) := by
  simpa only [dot, coeffWeight, Equiv.symm_apply_apply] using
    (Equiv.sum_comp π (fun j => w (π.symm j) * m j)).symm

theorem dot_coeffWeight_indicator (π : Fin 1024 ≃ Fin 1024)
    (I : Finset (Fin 1024)) (m : InitialMessage K) :
    dot (coeffWeight π (indicator I)) m = ∑ r ∈ I, m (π r) := by
  rw [dot_coeffWeight_left]
  simp only [indicator, dot, ite_mul, one_mul, zero_mul, ← Finset.sum_filter,
    Finset.filter_mem_eq_inter, Finset.univ_inter]

end
end AspisR0.Opening
