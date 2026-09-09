import GaoC1Recovery
import Mathlib.Logic.Equiv.Fin.Basic

/-! One shared sample suffices for all semantic C1 columns. This consumes the
proved arbitrary-word Gao decoder, rather than assuming decoder success.
Received values may already be totalized from authenticated raw bytes.
The code/source matrix and private-sampling law remain explicit interfaces. -/
set_option autoImplicit false
namespace AspisV8.CommonFibreGaoRecovery
open Finset Matrix
open AspisV8.GaoC1Recovery
variable {K : Type*} [Field K] [DecidableEq K]

def sampleFibre {m : ℕ} (j : Fin (m*4)) : Fin m :=
  (finProdFinEquiv.symm j).1

/-- The actual sample flattening is four consecutive slots per selected fibre. -/
theorem sampleFibre_flat {m : ℕ} (f : Fin m) (s : Fin 4) :
    sampleFibre (finProdFinEquiv (f,s)) = f := by
  simp [sampleFibre]

theorem flat_index {m : ℕ} (f : Fin m) (s : Fin 4) :
    (finProdFinEquiv (f,s)).val = 4*f.val+s.val := by
  simp [finProdFinEquiv, Nat.mul_comm, Nat.add_comm]

/-- Every erroneous scalar sample is in a bad complete fibre. The same set
can control arbitrarily many columns; its cardinality is not multiplied by
the number of columns. -/
theorem scalar_error_cap {m : ℕ} (bad : Finset (Fin m))
    (left right : Fin (m*4) → K)
    (outside : ∀ j, sampleFibre j ∉ bad → left j = right j) :
    (univ.filter fun j => left j ≠ right j).card ≤ 4*bad.card := by
  let cover := (bad.product (univ : Finset (Fin 4))).map finProdFinEquiv.toEmbedding
  have hsub : (univ.filter fun j => left j ≠ right j) ⊆ cover := by
    intro j hj
    have hb : sampleFibre j ∈ bad := by
      by_contra hn
      exact (mem_filter.mp hj).2 (outside j hn)
    apply mem_map.mpr
    refine ⟨finProdFinEquiv.symm j, ?_, finProdFinEquiv.apply_symm_apply j⟩
    exact mem_product.mpr ⟨hb, mem_univ _⟩
  have hc : cover.card = 4*bad.card := by
    simp [cover, Nat.mul_comm]
  exact hc ▸ card_le_card hsub

/-- Completeness for all sixteen semantic columns under ONE common bad-fibre
cap. An arbitrary corrupted received word is permitted. No valid-payment,
provider-return, candidate-membership or decoder-success hypothesis occurs. -/
theorem recover_all_columns {m : ℕ} (hn : 1025 ≤ m*4)
    (i h g : K) (hi : i^2 = -1) (hh : 2*h=1) (hg : 2*i*g=1)
    (bits : Bits) (coeff : Fin 16 → Row → K)
    (xs ys : Fin (m*4) → K) (received : Fin 16 → Fin (m*4) → K)
    (circles : ∀ j, (xs j)^2+(ys j)^2=1)
    (distinct : Function.Injective (fun j => xs j+i*ys j))
    (bad : Finset (Fin m)) (radius : 4*bad.card ≤ (m*4-1025)/2)
    (outside : ∀ col j, sampleFibre j ∉ bad →
      value bits (coeff col) (xs j) (ys j) = received col j)
    (tx ty : Row → K) (targetCircles : ∀ j, (tx j)^2+(ty j)^2=1)
    (B : Matrix Row Row K) (inverse : B*evaluationMatrix bits tx ty=1) :
    (fun col => recover bits i xs ys (received col) tx ty B) =
      (fun col => some (coeff col)) := by
  funext col
  apply recover_coefficients hn i h g hi hh hg bits (coeff col) xs ys
    (received col) circles distinct _ tx ty targetCircles B inverse
  exact (scalar_error_cap bad _ _ (outside col)).trans radius

/-- With 513 fibres the ambient RS code has 2052 scalar samples and unique
decoding radius 513. At most 128 touched fibres gives at most 512 errors. -/
theorem selected_radius (bad : Finset (Fin 513)) (cap : bad.card ≤ 128) :
    4*bad.card ≤ (513*4-1025)/2 := by omega

/-- Selected parameters: simultaneous coefficient recovery can fail only
when the shared sample contains at least 129 bad fibres, subject to the
stated algebraic/source interfaces. This is a deterministic implication,
not a sampling or acceptance probability theorem. -/
theorem selected_failure_requires_129
    (i h g : K) (hi : i^2 = -1) (hh : 2*h=1) (hg : 2*i*g=1)
    (bits : Bits) (coeff : Fin 16 → Row → K)
    (xs ys : Fin (513*4) → K) (received : Fin 16 → Fin (513*4) → K)
    (circles : ∀ j, (xs j)^2+(ys j)^2=1)
    (distinct : Function.Injective (fun j => xs j+i*ys j))
    (bad : Finset (Fin 513))
    (outside : ∀ col j, sampleFibre j ∉ bad →
      value bits (coeff col) (xs j) (ys j) = received col j)
    (tx ty : Row → K) (targetCircles : ∀ j, (tx j)^2+(ty j)^2=1)
    (B : Matrix Row Row K) (inverse : B*evaluationMatrix bits tx ty=1)
    (failure : (fun col => recover bits i xs ys (received col) tx ty B) ≠
      (fun col => some (coeff col))) : 129 ≤ bad.card := by
  by_contra hn
  apply failure
  exact recover_all_columns (by decide) i h g hi hh hg bits coeff xs ys
    received circles distinct bad (selected_radius bad (by omega)) outside
    tx ty targetCircles B inverse

#print axioms sampleFibre_flat
#print axioms flat_index
#print axioms scalar_error_cap
#print axioms recover_all_columns
#print axioms selected_radius
#print axioms selected_failure_requires_129
end AspisV8.CommonFibreGaoRecovery
