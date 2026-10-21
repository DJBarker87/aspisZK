import S7Kani3PhaseInvariant
set_option autoImplicit false
namespace S7Kani3Checkpoint
open AspisR1BatchedFoldSourceStep
open S7Kani3PhaseInvariant

/-- Each production TX constructs a fresh BatchedWeights with terms=0 from
canonical checkpoint weights. It does not carry the previous terms counter. -/
theorem reset_phase (raw : Nat) : Phase 0 (raw%modulus) := by
  have h := Nat.mod_lt raw (show 0<modulus by decide)
  dsimp [Phase,modulus] at *
  omega

/-- Algebraic TX1/finish/checkpoint/TX2 splice. The checkpoint's authenticated
source provenance is a separate obligation; this proves the exact reset law. -/
theorem transaction_splice (first second : List Nat) (terms raw : Nat) :
    run 0 (run terms raw first%modulus) second%modulus =
      run terms raw (first++second)%modulus := by
  rw [run_congruence,run_congruence,run_congruence,List.sum_append]
  rw [Nat.add_mod,Nat.add_mod,Nat.add_mod]
  simp only [Nat.mod_mod]
  rw [Nat.add_mod]
  simp only [Nat.mod_mod,Nat.add_assoc]

/-- Arbitrary initial checkpoint residue and term histories transport through
both intervals; the incoming state is required to agree modulo the field. -/
theorem checkpoint_congruence (first second : List Nat) (terms raw restored : Nat)
    (provenance : restored%modulus=run terms raw first%modulus) :
    run 0 restored second%modulus=run terms raw (first++second)%modulus := by
  rw [run_congruence,Nat.add_mod,provenance]
  rw [←Nat.add_mod]
  exact transaction_splice first second terms raw

#print axioms reset_phase
#print axioms transaction_splice
#print axioms checkpoint_congruence
end S7Kani3Checkpoint
