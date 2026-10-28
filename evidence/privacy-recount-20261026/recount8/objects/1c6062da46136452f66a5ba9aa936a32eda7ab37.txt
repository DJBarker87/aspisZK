import R1Z.ProverCommitCoinCall27
/-! Induction over the actual extracted digest operation. This retains
wrapping behavior on every path; natural-cursor agreement has an explicit
arithmetic room condition, distinct from execution equality. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitCoinSequence27
open Aeneas Aeneas.Std Result AspisR1CoinEffect27
open ProverCommitCoinTape27 ProverCommitCoinCall27
attribute [local instance] Classical.propDecidable
abbrev Parts := ProverCommitOracleEffect26.Parts
abbrev Bytes32 := ProverCommitCoinCall27.Bytes32

structure Run (Value : Type) where
  value : Value
  state : Machine
  history : List (Parts × Bytes32)

def evaluate {Value : Type} : Program Parts Bytes32 Value → Machine → Result (Run Value)
  | .done value,s => ok ⟨value,s,[]⟩
  | .call parts next,s => do
    let (answer,s') ← CoinOracle.Insts.Effect27EffectDigest32CoinState.digest mapRecording s parts
    let tail ← evaluate (next answer) s'
    ok {tail with history := (parts,answer)::tail.history}

def referenceRun {Value : Type} : Program Parts Bytes32 Value → Machine → Run Value
  | .done value,s => ⟨value,s,[]⟩
  | .call parts next,s =>
    let (answer,s') := expected s parts
    let tail := referenceRun (next answer) s'
    {tail with history := (parts,answer)::tail.history}

/-- Every extracted call, final recording/collision state and ordered query
history agree, for arbitrary finite adaptive programs, without a success premise. -/
theorem generated_sequence {Value : Type} (p : Program Parts Bytes32 Value) (s : Machine) :
    evaluate p s = ok (referenceRun p s) := by
  induction p generalizing s with
  | done value => rfl
  | call parts next ih =>
    simp only [evaluate,call_exact,bind_tc_ok]
    cases step : expected s parts with
    | mk answer state =>
      simp only [Aeneas.Std.uncurry]
      rw [ih]
      simp only [bind_tc_ok,referenceRun,step,Aeneas.Std.uncurry]

/-- No probabilistic exception is introduced by a cursor representation.
Below wrap, the extracted machine's entire state is the Nat reference state. -/
theorem step_view (s : Machine) (parts : Parts)
    (room : s.next.val+1 < UScalar.size .Usize) :
    ( (expected s parts).1, view (expected s parts).2 ) =
      reference (view s) (ProverCommitStreamBytes.wireBytes parts) := by
  have next : (Usize.wrapping_add s.next 1#usize).val = s.next.val+1 := by
    rw [Usize.wrapping_add_val_eq]
    have one : (1#usize).val = 1 := by scalar_tac
    rw [one,Nat.mod_eq_of_lt room]
  unfold expected view reference answer
  simp only [next]

#print axioms generated_sequence
#print axioms step_view
end R1Z.ProverCommitCoinSequence27
