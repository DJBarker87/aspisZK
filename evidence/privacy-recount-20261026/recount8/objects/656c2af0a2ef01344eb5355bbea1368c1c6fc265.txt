import R1Z.ProverCommitSeedEvent19

/-! Reservation ROM coordinates. The fresh-coordinate theorem is a P1 model
fact, not a source-to-ROM transport. The existing simulator seed event does
not contain reservation-input queries. No new cryptographic premise. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitReservationRom37
open R0Z R0Z.FsStatement R0Z.FsAbort R0Z.FsGood R0Z.HvzkV
attribute [local instance] Classical.propDecidable

def reservationDomain : List UInt8 := [97, 115, 112, 105, 115, 58, 115, 116, 97, 116, 101, 45, 111, 110, 108, 121, 58, 97, 116, 116, 101, 109, 112, 116, 45, 114, 101, 115, 101, 114, 118, 97, 116, 105, 111, 110, 58, 118, 49]
def reservationInput (nonce : OracleAnswer) : List UInt8 :=
  reservationDomain ++ List.ofFn nonce

theorem reservation_length (nonce : OracleAnswer) :
    (reservationInput nonce).length = 71 := by
  simp [reservationInput,reservationDomain]

/-- Unlike a global table marginal, this fixes *all* other ROM coordinates.
The entries can depend arbitrarily on that fixed context. -/
theorem entry_mass (entries : List OracleAnswer) :
    eventMass (fun answer : OracleAnswer => answer ∈ entries) ≤
      (entries.length : ℚ) / (2 : ℚ)^256 := by
  induction entries with
  | nil => simp [eventMass,mean_const]
  | cons entry entries ih =>
    have sub : (fun answer : OracleAnswer => answer ∈ entry::entries) =
        fun answer => answer = entry ∨ answer ∈ entries := by
      funext answer
      simp only [List.mem_cons]
    rw [sub]
    have h := (R0Z.FsAbortBounds.mass_or_le _ _).trans (add_le_add
      (le_of_eq (QueryScanSharedHistoryMass.point_mass entry)) ih)
    rw [QueryScanSharedHistoryMass.answer_cardinality,Nat.cast_pow,Nat.cast_ofNat] at h
    exact h.trans (le_of_eq (by simp only [List.length_cons,Nat.cast_add,Nat.cast_one]; ring))

theorem fresh_coordinate {A : Type} [DecidableEq A] (a : A)
    (rest : {j : A // j ≠ a} → OracleAnswer) (entries : List OracleAnswer) :
    eventMass (fun digest : OracleAnswer =>
      (LazyTable.splitAt a).symm (digest,rest) a ∈ entries) ≤
      (entries.length : ℚ) / (2 : ℚ)^256 := by
  simpa [LazyTable.splitAt] using entry_mass entries

theorem prior_preserved {A : Type} [DecidableEq A] (a : A)
    (rest : {j : A // j ≠ a} → OracleAnswer) (digest : OracleAnswer)
    (j : A) (fresh : j ≠ a) :
    (LazyTable.splitAt a).symm (digest,rest) j = rest ⟨j,fresh⟩ := by
  simp [LazyTable.splitAt,fresh]

/-- A concrete reservation frame starts with ASCII a (97), whereas the
existing private simulator coin prefix starts with ASCII U (85). -/
theorem not_simulator_seedPoint (nonce seed : OracleAnswer) :
    ¬ ProverCommitSeedEvent19.seedPoint (reservationInput nonce) seed := by
  intro h
  have heads := congrArg List.head? h
  change some (97 : UInt8) = some (85 : UInt8) at heads
  cases heads

def reservationQueried (queries : List ProverCommitSeedEvent19.Entry)
    (nonce : OracleAnswer) : Prop :=
  ∃ entry ∈ queries, entry.1 = reservationInput nonce

/-- An exact memo-hit is absent from the existing seed event, for every
simulator seed and nonce. This is a counterexample to event containment,
not a collision or privacy attack. It also holds for nonzero nonces. -/
theorem queried_not_seedGuess (nonce seed : OracleAnswer) :
    reservationQueried [(reservationInput nonce,0)] nonce ∧
      ¬ ProverCommitSeedEvent19.seedGuess [(reservationInput nonce,0)] seed := by
  constructor
  · exact ⟨(reservationInput nonce,0),by simp,rfl⟩
  · intro h
    obtain ⟨entry,member,point⟩ := h
    have eq : entry = (reservationInput nonce,0) := by simpa using member
    subst entry
    exact not_simulator_seedPoint nonce seed point

theorem no_existing_event_containment (nonce seed : OracleAnswer) :
    ¬ ∀ queries : List ProverCommitSeedEvent19.Entry,
      reservationQueried queries nonce → ProverCommitSeedEvent19.seedGuess queries seed := by
  intro h
  have counter := queried_not_seedGuess nonce seed
  exact counter.2 (h _ counter.1)

#print axioms reservation_length
#print axioms entry_mass
#print axioms fresh_coordinate
#print axioms prior_preserved
#print axioms not_simulator_seedPoint
#print axioms queried_not_seedGuess
#print axioms no_existing_event_containment
end R1Z.ProverCommitReservationRom37
