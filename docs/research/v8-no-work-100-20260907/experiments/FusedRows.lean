import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic

/-! Exact coefficientwise fusion of two rows differing in one arity-four block.
Theorem applies to arbitrary coefficients and arbitrary linear transport,
including chord transpose and the composed four dual folds once instantiated.
This is not an Aeneas translation of the Rust carry implementation. -/
set_option autoImplicit false
namespace AspisV8.FusedRows
variable {K : Type*} [CommRing K]

def block (x y : Fin 2 → K) : Fin 4 → K :=
  ![x 0 * y 0, x 1 * y 0, x 0 * y 1, x 1 * y 1]

theorem complement_block (x y : Fin 2 → K) (d : Fin 4) :
    block (fun i => x i.rev) (fun i => y i.rev) d = block x y d.rev := by
  fin_cases d <;> rfl

def tensor (b : Fin 5 → Fin 4 → K) : (Fin 5 → Fin 4) → K :=
  fun digits => ∏ j, b j (digits j)

def rest (b : Fin 5 → Fin 4 → K) (digits : Fin 5 → Fin 4) : K :=
  ∏ j ∈ (Finset.univ.erase (1 : Fin 5)), b j (digits j)

theorem tensor_factor (b : Fin 5 → Fin 4 → K) (digits : Fin 5 → Fin 4) :
    tensor b digits = b 1 (digits 1) * rest b digits := by
  exact (Finset.mul_prod_erase (Finset.univ) (fun j => b j (digits j))
    (Finset.mem_univ (1 : Fin 5))).symm

theorem tensor_update (b : Fin 5 → Fin 4 → K) (newBlock : Fin 4 → K)
    (digits : Fin 5 → Fin 4) :
    tensor (Function.update b 1 newBlock) digits =
      newBlock (digits 1) * rest b digits := by
  rw [tensor_factor]
  simp only [Function.update_self]
  congr 1

theorem fuse_coefficients (b : Fin 5 → Fin 4 → K) (s t : K) :
    tensor (Function.update b 1 (fun d => s * b 1 d + t * b 1 d.rev)) =
      s • tensor b + t • tensor (Function.update b 1 (fun d => b 1 d.rev)) := by
  funext digits
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [tensor_update, tensor_factor, tensor_update]
  ring

theorem fuse_through_linear_transport {V : Type*} [AddCommGroup V] [Module K V]
    (L : ((Fin 5 → Fin 4) → K) →ₗ[K] V) (b : Fin 5 → Fin 4 → K) (k : K) :
    L (tensor (Function.update b 1 (fun d => k * b 1 d + k^3 * b 1 d.rev))) =
      k • L (tensor b) + k^3 • L (tensor (Function.update b 1 (fun d => b 1 d.rev))) := by
  rw [fuse_coefficients, map_add, map_smul, map_smul]

#print axioms complement_block
#print axioms tensor_factor
#print axioms tensor_update
#print axioms fuse_coefficients
#print axioms fuse_through_linear_transport
end AspisV8.FusedRows
