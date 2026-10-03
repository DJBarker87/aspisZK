import AspisV8R19.R443BoundedRejectionMass

set_option autoImplicit false
namespace AspisV8R19.R445InitialBlockRejectionLaw
open OracleResampling R442RejectionAlphabet R443BoundedRejectionMass
open R421UniformMasked31Block
noncomputable section

def decodeTapeEquiv (p n : Nat) : (Fin n → Fin (p+1)) ≃ Tape p n :=
  Equiv.piCongrRight (fun _ => alphabetEquiv p)

theorem uniform_decoded_tape (p n : Nat) (f : Option (Fin p) → ℚ) :
    mean (fun w : Fin n → Fin (p+1) => f (run n (decodeTapeEquiv p n w))) =
      mean (fun t : Tape p n => f (run n t)) := by
  exact mean_equiv (decodeTapeEquiv p n) (fun t => f (run n t))

abbrev modulus : Nat := 2147483647

/-- First acceptance in the eight masked words of one initial source block.
This definition imposes no oracle freshness law. -/
def initialBlockResult (block : SourceDuplexStep.State) : Option (Fin modulus) :=
  run 8 (decodeTapeEquiv modulus 8 ((splitBlock31Equiv block).2))

theorem initial_block_mean (f : Option (Fin modulus) → ℚ) :
    mean (fun block : SourceDuplexStep.State => f (initialBlockResult block)) =
      mean (fun t : Tape modulus 8 => f (run 8 t)) := by
  unfold initialBlockResult
  calc
    _ = mean (fun q : (Fin 8 → Fin 2) × (Fin 8 → Fin (2^31)) =>
        f (run 8 (decodeTapeEquiv modulus 8 q.2))) :=
      (mean_equiv splitBlock31Equiv
        (fun q => f (run 8 (decodeTapeEquiv modulus 8 q.2)))).symm
    _ = mean (fun w : Fin 8 → Fin (2^31) =>
        f (run 8 (decodeTapeEquiv modulus 8 w))) := by
      rw [mean_prod (fun (_ : Fin 8 → Fin 2) (w : Fin 8 → Fin (2^31)) =>
        f (run 8 (decodeTapeEquiv modulus 8 w)))]
      exact mean_const _
    _ = _ := uniform_decoded_tape modulus 8 f

theorem initial_block_failure :
    mean (fun block : SourceDuplexStep.State =>
      if initialBlockResult block = none then (1 : ℚ) else 0) =
      (1 / (2147483648 : ℚ)) ^ 8 := by
  rw [initial_block_mean]
  exact failure_mass modulus 8

theorem initial_block_value (a : Fin modulus) :
    mean (fun block : SourceDuplexStep.State =>
      if initialBlockResult block = some a then (1 : ℚ) else 0) =
      (1 - (1 / (2147483648 : ℚ)) ^ 8) / 2147483647 := by
  rw [initial_block_mean]
  exact value_mass modulus 8 a

#print axioms uniform_decoded_tape
#print axioms initial_block_mean
#print axioms initial_block_failure
#print axioms initial_block_value
end
end AspisV8R19.R445InitialBlockRejectionLaw
