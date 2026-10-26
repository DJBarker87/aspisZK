import AspisV8R19.R406SamplerWordDistribution
import Mathlib.Algebra.BigOperators.Fin

/-!
Uniformity of the source's masked 31-bit word block under the uniform 32-byte
tape model. This draft only transports a finite mean along explicit
bijections; it does not assert independence or freshness for a shared oracle.
-/
set_option autoImplicit false
namespace AspisV8R19.R421UniformMasked31Block

open DuplexFrames SourceDuplexStep SamplerWords OracleResampling
open R406SamplerWordDistribution
noncomputable section

/-- Split a 32-bit word into its high bit and low 31 bits. -/
def splitWord31Equiv : Fin (2^32) ≃ (Fin 2 × Fin (2^31)) :=
  (finProdFinEquiv (m := 2) (n := 2^31)).symm

def distribute31 : (Fin 8 → Fin 2 × Fin (2^31)) ≃
    ((Fin 8 → Fin 2) × (Fin 8 → Fin (2^31))) where
  toFun f := (fun j => (f j).1, fun j => (f j).2)
  invFun p j := (p.1 j, p.2 j)
  left_inv _ := rfl
  right_inv _ := rfl

def splitBlock31Equiv : State ≃
    ((Fin 8 → Fin 2) × (Fin 8 → Fin (2^31))) :=
  (blockWordEquiv.trans (Equiv.piCongrRight (fun _ => splitWord31Equiv))).trans distribute31

theorem masked31_value (block : State) (j : Fin 8) :
    ((splitBlock31Equiv block).2 j).val = masked 31 (word block j) := by
  change (blockWordEquiv block j).val % 2^31 = _
  rw [word_value, masked_eq_mod]

theorem words31_value (block : State) :
    words 31 block = List.ofFn (fun j => ((splitBlock31Equiv block).2 j).val) := by
  unfold words
  congr 1
  funext j
  exact (masked31_value block j).symm

theorem uniform_masked31_block (f : List Nat → ℚ) :
    mean (fun out : State => f (words 31 out)) =
      mean (fun x : Fin 8 → Fin (2^31) =>
        f (List.ofFn (fun j => (x j).val))) := by
  simp_rw [words31_value]
  rw [mean_equiv splitBlock31Equiv
    (fun p => f (List.ofFn (fun j => (p.2 j).val)))]
  rw [mean_prod (fun (_ : Fin 8 → Fin 2) (x : Fin 8 → Fin (2^31)) =>
    f (List.ofFn (fun j => (x j).val)))]
  exact mean_const _

#print axioms masked31_value
#print axioms words31_value
#print axioms uniform_masked31_block

end
end AspisV8R19.R421UniformMasked31Block
