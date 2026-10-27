import R1Z.ProverCommitEntropy18
/-! Compose one-draw source-slice certificates over the exact sixteen-step
schedule. OS errors and successful draws remain absorbing, with retained
state; the OS law is not assumed by this control-flow induction. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitEntropyStep19
open R0Z.FsStatement R1Z.GamesR1PBin R1Z.ProverCommitEntropy18
attribute [local instance] Classical.propDecidable

theorem reject_block (raw : Candidate) (i : Fin 3) (zero : raw i = 0) :
    decode raw = none := by
  unfold decode
  rw [dif_neg (fun good => good i zero)]

/-- A single rejected draw consumes one state transition and no retry. -/
theorem rejected_step {State OsError : Type}
    (next : State → Except OsError Candidate × State) (state after : State)
    (raw : Candidate) (fuel : Nat)
    (drawn : next state = (.ok raw,after)) (invalid : decode raw = none) :
    run next (fuel+1) state = run next fuel after := by
  simp only [run,drawn,invalid]

/-- Arbitrary rejected blocks may differ at every draw. Exactly `fuel` draws
are consumed; no draw after the exhausted boundary is inspected. -/
theorem rejected_prefix {State OsError : Type}
    (next : State → Except OsError Candidate × State) (states : Nat → State)
    (draws : Nat → Candidate) (fuel start : Nat)
    (drawn : ∀ j < fuel, next (states (start+j)) = (.ok (draws (start+j)),states (start+j+1)))
    (invalid : ∀ j < fuel, decode (draws (start+j)) = none) :
    run next fuel (states start) = (.error .repeatedZero,states (start+fuel)) := by
  induction fuel generalizing start with
  | zero => simp only [run,Nat.add_zero]
  | succ fuel ih =>
    have first := drawn 0 (Nat.zero_lt_succ fuel)
    have bad := invalid 0 (Nat.zero_lt_succ fuel)
    simp only [Nat.add_zero] at first bad
    rw [rejected_step next _ _ _ fuel first bad]
    have tailDraw : ∀ j < fuel, next (states (start+1+j)) =
        (.ok (draws (start+1+j)),states (start+1+j+1)) := by
      intro j hj
      simpa only [Nat.add_assoc,Nat.add_comm 1 j] using drawn (j+1) (by omega)
    have tailBad : ∀ j < fuel, decode (draws (start+1+j)) = none := by
      intro j hj
      simpa only [Nat.add_assoc,Nat.add_comm 1 j] using invalid (j+1) (by omega)
    simpa only [Nat.add_assoc,Nat.add_comm 1 fuel] using ih (start+1) tailDraw tailBad

/-- The Kani per-block source-step checks instantiate this induction for
sixteen arbitrary rejected candidates, with the exact final draw cursor. -/
theorem sixteen_rejected {State OsError : Type}
    (next : State → Except OsError Candidate × State) (states : Nat → State)
    (draws : Nat → Candidate) (blocks : Nat → Fin 3)
    (drawn : ∀ j < 16, next (states j) = (.ok (draws j),states (j+1)))
    (invalid : ∀ j < 16, draws j (blocks j) = 0) :
    generate next (states 0) = (.error .repeatedZero,states 16) := by
  exact rejected_prefix next states draws 16 0
    (by simpa only [Nat.zero_add] using drawn)
    (fun j hj => by simpa only [Nat.zero_add] using reject_block _ (blocks j) (invalid j hj))

#print axioms reject_block
#print axioms rejected_step
#print axioms rejected_prefix
#print axioms sixteen_rejected
end R1Z.ProverCommitEntropyStep19
