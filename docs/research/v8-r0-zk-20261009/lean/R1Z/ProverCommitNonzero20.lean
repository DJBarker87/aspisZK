import R1Z.ProverCommitSimulatorCoin18
import R1Z.ProverCommitSeedEvent19
/-! A finite-schedule obstruction, not a counterexample to existence of a
coupling. Coins::nonzero has no source cap; its addresses use a wrapping U64. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitNonzero20
open Aeneas Aeneas.Std Result ProverCommitSimulatorCoin18
attribute [local instance] Classical.propDecidable

def zeroHash (zero : Bytes32) : Hash := fun _ => ok zero

def search (zero : Bytes32) (hash : Hash) (seed : Bytes32) (attempt : U32) (stream : U8) :
    Nat → U64 → Result (Option (Bytes32 × U64))
  | 0, _ => ok none
  | n+1, counter => do
    let (answer,next) ← AspisR1SimulatorCoin18.sim.coin_owned18 hash seed attempt stream counter
    if answer=zero then search zero hash seed attempt stream n next
    else ok (some (answer,next))

/-- Any finite unfolding of the actual extracted coin transition can fail to
supply a nonzero answer. The callback is a single consistent zero oracle. -/
theorem zero_prefix (zero : Bytes32) (n : Nat) (seed : Bytes32) (attempt : U32) (stream : U8) (counter : U64) :
    search zero (zeroHash zero) seed attempt stream n counter=ok none := by
  induction n generalizing counter with
  | zero => rfl
  | succ n ih =>
    simp only [search,extracted_step,zeroHash,bind_tc_ok]
    change (if zero=zero then
      search zero (zeroHash zero) seed attempt stream n (U64.wrapping_add counter 1#u64)
      else ok (some (zero,U64.wrapping_add counter 1#u64))) = ok none
    rw [if_pos rfl]
    exact ih _

theorem no_uniform_finite_bound (zero : Bytes32) (n : Nat) (seed : Bytes32) (attempt : U32) (stream : U8)
    (counter : U64) :
    ¬ (∀ hash : Hash, ∃ result, search zero hash seed attempt stream n counter=ok (some result)) := by
  intro all
  obtain ⟨result,h⟩ := all (zeroHash zero)
  rw [zero_prefix] at h
  cases h

/-- No-query observers have no seed-query exception. This does not assert
that all other selectedBad events vanish, nor refute an entire RunJoin. -/
theorem empty_observer_no_seed_guess (seed : R0Z.FsStatement.OracleAnswer) :
    ¬ ProverCommitSeedEvent19.seedGuess [] seed := by
  rintro ⟨entry,member,_⟩
  cases member

#print axioms zero_prefix
#print axioms no_uniform_finite_bound
#print axioms empty_observer_no_seed_guess
end R1Z.ProverCommitNonzero20
