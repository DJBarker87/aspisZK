import R1Z.ProverCommitReservationFrames37
import R1Z.ProverCommitReservationNonzero37

/-! Explicit D150 event on one fresh ROM coordinate, conditional on a fixed
byte-blind context. This is not a source selected-nonce or adaptive-history
refinement. In particular the ledger size is a visible parameter. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitReservationGuess38
open R0Z R0Z.FsStatement R0Z.FsAbort R0Z.FsGood R0Z.HvzkV
open GamesR1PBin ProverCommitReservationRom37
local instance (priority := 10000) allDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p
local instance (priority := 10000) allDecEq (U : Type) : DecidableEq U := Classical.decEq U

def budget (queries entries attempts : Nat) : ℚ :=
  ((queries : ℚ) + entries) * attempts / ((2 : ℚ)^256 - 1)

/-- The path argument is the digest naming the private reservation file.
Queries are the adversary's own input bytes; malformed inputs are allowed. -/
def reservationGuess (queries : List (List UInt8)) (entries : List OracleAnswer)
    (nonce : NZ) (path : OracleAnswer) : Prop :=
  reservationInput nonce.val ∈ queries ∨ path ∈ entries

theorem answer_card : Fintype.card OracleAnswer = 2^256 := by
  have all : ∀ j : Fintype OracleAnswer, @Fintype.card OracleAnswer j = 2^256 := fun j =>
    (congrArg (@Fintype.card OracleAnswer) (Subsingleton.elim j _)).trans
      QueryScanSharedHistoryMass.answer_cardinality
  exact all _

theorem nonzero_card : Fintype.card NZ = 2^256 - 1 := by
  change Fintype.card {x : OracleAnswer // ¬ x = 0} = _
  rw [Fintype.card_subtype_compl,answer_card]
  simp

theorem query_point (input : List UInt8) :
    eventMass (fun nonce : NZ => reservationInput nonce.val = input) ≤
      1 / ((2 : ℚ)^256 - 1) := by
  by_cases exists_nonce : ∃ nonce : NZ, reservationInput nonce.val = input
  · obtain ⟨nonce, hn⟩ := exists_nonce
    have h := eventMass_mono
      (fun n : NZ => reservationInput n.val = input) (fun n => n = nonce)
      (fun n hit => Subtype.ext
        (ProverCommitReservationFrames37.reservation_injective (hit.trans hn.symm)))
    rw [QueryScanSharedHistoryMass.point_mass, nonzero_card] at h
    rw [Nat.cast_sub (by norm_num : 1 ≤ (2:Nat)^256),
      Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one] at h
    exact h
  · have empty : (fun nonce : NZ => reservationInput nonce.val = input) =
        fun _ => False := by
      funext n
      exact propext ⟨fun hit => exists_nonce ⟨n,hit⟩,False.elim⟩
    rw [empty]
    simp only [eventMass,if_false,mean_const]
    norm_num

theorem query_list (queries : List (List UInt8)) :
    eventMass (fun nonce : NZ => reservationInput nonce.val ∈ queries) ≤
      queries.length / ((2 : ℚ)^256 - 1) := by
  induction queries with
  | nil => simp [eventMass,mean_const]
  | cons q qs ih =>
    have shape : (fun nonce : NZ => reservationInput nonce.val ∈ q::qs) =
        fun nonce => reservationInput nonce.val = q ∨ reservationInput nonce.val ∈ qs := by
      funext n
      simp only [List.mem_cons]
    rw [shape]
    exact ((R0Z.FsAbortBounds.mass_or_le _ _).trans
      (add_le_add (query_point q) ih)).trans (le_of_eq (by
        simp only [List.length_cons,Nat.cast_add,Nat.cast_one]; ring))

theorem path_list (entries : List OracleAnswer) :
    eventMass (fun path : OracleAnswer => path ∈ entries) ≤
      entries.length / ((2 : ℚ)^256 - 1) := by
  induction entries with
  | nil => simp [eventMass,mean_const]
  | cons path entries ih =>
    have shape : (fun p : OracleAnswer => p ∈ path::entries) =
        fun p => p = path ∨ p ∈ entries := by
      funext p
      simp only [List.mem_cons]
    have hp : eventMass (fun p : OracleAnswer => p = path) ≤
        1 / ((2 : ℚ)^256 - 1) := by
      rw [QueryScanSharedHistoryMass.point_mass,
        answer_card,Nat.cast_pow,Nat.cast_ofNat]
      exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
    rw [shape]
    exact ((R0Z.FsAbortBounds.mass_or_le _ _).trans
      (add_le_add hp ih)).trans (le_of_eq (by
        simp only [List.length_cons,Nat.cast_add,Nat.cast_one]; ring))

/-- P1 supplies a fresh uniform digest when the input was not queried.
This product calculation also charges queried inputs, so the ignored digest
on a memo hit cannot silently be used as its real oracle answer. -/
theorem fresh_slice (queries : List (List UInt8)) (entries : List OracleAnswer) :
    eventMass (fun r : NZ × OracleAnswer => reservationGuess queries entries r.1 r.2) ≤
      budget queries.length entries.length 1 := by
  have hq : eventMass (fun r : NZ × OracleAnswer =>
      reservationInput r.1.val ∈ queries) =
      eventMass (fun nonce : NZ => reservationInput nonce.val ∈ queries) := by
    exact CouplingR1PBin.mp_fst (X := NZ) (Y := OracleAnswer)
      (fun nonce => if reservationInput nonce.val ∈ queries then (1 : ℚ) else 0)
  have he : eventMass (fun r : NZ × OracleAnswer => r.2 ∈ entries) =
      eventMass (fun path : OracleAnswer => path ∈ entries) := by
    exact CouplingR1PBin.mp_snd (X := NZ) (Y := OracleAnswer)
      (fun path => if path ∈ entries then (1 : ℚ) else 0)
  have h := R0Z.FsAbortBounds.mass_or_le
    (fun r : NZ × OracleAnswer => reservationInput r.1.val ∈ queries)
    (fun r => r.2 ∈ entries)
  change eventMass (fun r : NZ × OracleAnswer => reservationGuess queries entries r.1 r.2) ≤
    eventMass (fun r : NZ × OracleAnswer => reservationInput r.1.val ∈ queries) +
    eventMass (fun r : NZ × OracleAnswer => r.2 ∈ entries) at h
  rw [hq,he] at h
  exact (h.trans (add_le_add (query_list queries) (path_list entries))).trans
    (le_of_eq (by unfold budget; ring))

/-- A union over actual attempted reservations needs no independence between
attempt events, but still needs their conditional/fresh-slice instantiation.
This deliberately does not assert that eight source retries already supply it. -/
theorem attempt_union {M : Type} [Fintype M] [Nonempty M]
    (attempts queries entries : Nat) (bad : Fin attempts → M → Prop)
    (per_attempt : ∀ i, eventMass (bad i) ≤ budget queries entries 1) :
    eventMass (fun m => ∃ i, bad i m) ≤ budget queries entries attempts := by
  have h := R0Z.FsAbortBounds.mass_exists_le_card bad (budget queries entries 1)
    per_attempt
  rw [Fintype.card_fin] at h
  simpa only [R0Z.FsAbortBounds.mass,eventMass] using
    h.trans (le_of_eq (by unfold budget; ring))

#print axioms answer_card
#print axioms nonzero_card
#print axioms query_point
#print axioms query_list
#print axioms path_list
#print axioms fresh_slice
#print axioms attempt_union
end R1Z.ProverCommitReservationGuess38
