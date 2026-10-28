import R1Z.ProverCommitLedger36

/-! D151 exact private-ledger coupling, with no cardinality hypothesis.
The address is evaluated in the same ROM in both worlds. These are prefix
laws; successful witness-dependent continuations are not equated. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitLedgerCoupling39
open ProverCommitLedger36 ProverCommitEntropy18

/-- A fixed shared ROM and nonce give literally the same reservation state
transition, including byte-blind injected additions and faults. -/
theorem same_reservation (address : Path → Path) (schedule : Schedule)
    (unix : Bool) (nonce : Path) (s t : State) (shared : s = t) :
    reserve schedule unix (address nonce) s = reserve schedule unix (address nonce) t := by
  rw [shared]

/-- Membership is tested after this call's adversarial additions. No ledger
entry is classified as a probabilistic privacy failure. -/
theorem collision_duplicate (address : Path → Path) (schedule : Schedule)
    (unix : Bool) (nonce : Path) (s : State)
    (collision : address nonce ∈
      (inject (schedule s.history.length .create s.history) s).ledger) :
    reserve schedule unix (address nonce) s =
      (.error .duplicate,
        (createNew (address nonce) (schedule s.history.length .create s.history) s).2) := by
  have hit := (alreadyExists_iff (address nonce) _ s).2 collision
  simp only [reserve,hit]

/-- Same candidate tape, selection rule, fault history and private ledger
couple the whole preparation prefix exactly, for arbitrary ledger size. -/
theorem same_preparation (address : Path → Path) (schedule : Schedule)
    (tape : Nat → Candidate) (unix : Bool) (s t : State) (shared : s = t) :
    prepare address schedule tape unix s = prepare address schedule tape unix t := by
  rw [shared]

/-- A duplicate preparation cannot call either witness-dependent continuation.
Both returned error and full retained environment state coincide. -/
theorem duplicate_fail_closed {Witness Proof : Type} (address : Path → Path)
    (schedule : Schedule) (tape : Nat → Candidate) (unix : Bool)
    (s after : State)
    (failed : prepare address schedule tape unix s =
      (.error (.reservation .duplicate),after))
    (w : Witness)
    (real : Witness → ProverCommitEnvironment35.Secret → State → Except ProverCommitEnvironment35.Error Proof × State)
    (ideal : Unit → ProverCommitEnvironment35.Secret → State → Except ProverCommitEnvironment35.Error Proof × State) :
    withPrepared address schedule tape unix s w real =
      withPrepared address schedule tape unix s () ideal := by
  rw [fail_closed address schedule tape unix s after _ failed w real,
    fail_closed address schedule tape unix s after _ failed () ideal]

#print axioms same_reservation
#print axioms collision_duplicate
#print axioms same_preparation
#print axioms duplicate_fail_closed
end R1Z.ProverCommitLedgerCoupling39
