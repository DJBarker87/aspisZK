import R1Z.ProverCommitEntropyJoin18
import R1Z.ProverCommitEntropyStep19
import R1Z.ProverCommitEntropySymmetry18
import R1Z.CommitReadsR1
import R1Z.QueryScanSharedHistoryMass
/-! Explicit entropy bad events. No OS law or durable-store guarantee is
assumed. The numerical zero-draw bound below is for the stated uniform finite
raw carrier, not the OS. It conservatively uses the first rejected 96-byte
candidate, so no independence of later draws is needed for that upper bound. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitEntropy34
open R0Z R0Z.FsStatement R0Z.FsAbort R0Z.FsGood R0Z.HvzkV
open ProverCommitEntropy18 ProverCommitEntropyJoin18
attribute [local instance] Classical.propDecidable

variable {State OsError R : Type}

def osBad (next : State → Except OsError Candidate × State) (initial : R → State)
    (r : R) : Prop := ∃ e, (generate next (initial r)).1 = .error (.os e)

def zeroBad (next : State → Except OsError Candidate × State) (initial : R → State)
    (r : R) : Prop := (generate next (initial r)).1 = .error .repeatedZero

def failed (next : State → Except OsError Candidate × State) (initial : R → State)
    (r : R) : Prop := ∃ e, (generate next (initial r)).1 = .error e

/-- These are exact masses of the specified runtime law; no numerical OS
availability assertion is smuggled into the uniform zero-draw result. -/
def osMass [Fintype R] (next : State → Except OsError Candidate × State)
    (initial : R → State) : ℚ := eventMass (osBad next initial)
def zeroMass [Fintype R] (next : State → Except OsError Candidate × State)
    (initial : R → State) : ℚ := eventMass (zeroBad next initial)

theorem bad_disjoint (next : State → Except OsError Candidate × State)
    (initial : R → State) (r : R) : ¬ (osBad next initial r ∧ zeroBad next initial r) := by
  rintro ⟨⟨e,he⟩,hz⟩
  unfold zeroBad at hz
  rw [he] at hz
  cases hz

theorem failure_mass [Fintype R] (next : State → Except OsError Candidate × State)
    (initial : R → State) :
    eventMass (failed next initial) = osMass next initial + zeroMass next initial := by
  unfold osMass zeroMass
  unfold eventMass
  rw [← R0Z.FsAbortBounds.mean_add'']
  congr 1
  funext r
  unfold failed osBad zeroBad
  cases hg : (generate next (initial r)).1 with
  | ok secret => simp
  | error e => cases e <;> simp

/-- An OS error on the first call has mass one under an all-failing OS law.
The source signature/control alone therefore gives no subunit OS bound. -/
theorem always_os_mass [Fintype R] [Nonempty R] (initial : R → State)
    (error : OsError) :
    osMass (fun s => (.error error,s)) initial = 1 := by
  unfold osMass osBad generate
  simp [run,eventMass,mean_const]

theorem no_universal_os_bound (δ : ℚ) (hδ : δ < 1) :
    ¬ ∀ next : Unit → Except Unit Candidate × Unit,
      osMass next (fun _ : Unit => ()) ≤ δ := by
  intro bound
  have h := bound (fun s => (.error (),s))
  rw [always_os_mass] at h
  exact (not_le_of_gt hδ) h

theorem decode_none_iff (raw : Candidate) :
    decode raw = none ↔ ∃ i, raw i = 0 := by
  unfold decode
  split
  next good =>
    simp only [Option.some_ne_none, false_iff, not_exists]
    exact good
  next bad =>
    simp only [true_iff]
    simpa only [not_forall,not_not] using bad

def zeroBudget : ℚ := 3 / (2 : ℚ)^256

/-- Each of the three 32-byte slices has point mass 2^-256 in this uniform
carrier. The union bound needs no independence between the three events. -/
theorem candidate_bad_mass : eventMass (fun raw : Candidate => decode raw = none) ≤ zeroBudget := by
  have h := R0Z.FsAbortBounds.mass_exists_le_card
    (fun i : Fin 3 => fun raw : Candidate => raw i = 0) (1 / (2 : ℚ)^256)
    (fun i => by
      rw [CommitReadsR1.mass_coord (N := 3) (X := OracleAnswer) i
        (fun a : OracleAnswer => a = 0)]
      rw [R0Z.FsAbortBounds.mass_point,QueryScanSharedHistoryMass.answer_cardinality,
        Nat.cast_pow,Nat.cast_ofNat])
  have equal : (fun raw : Candidate => decode raw = none) = fun raw => ∃ i, raw i = 0 :=
    funext fun raw => propext (decode_none_iff raw)
  rw [equal]
  simpa only [eventMass,R0Z.FsAbortBounds.mass,Fintype.card_fin,Nat.cast_ofNat,
    zeroBudget,div_eq_mul_inv,one_mul] using h

theorem zero_failure_first (raw : RawRand)
    (hz : rawGenerate raw = .error .repeatedZero) : decode (raw 0) = none := by
  cases hd : decode (raw 0) with
  | none => rfl
  | some secret =>
    have erase := ProverCommitEntropySymmetry18.erase_of_decode (raw 0) secret hd
    have drawn : rawNext raw 0 = (.ok (fun i => (secret i).val),1) := by
      change ((Except.ok (raw 0) : Except Unit Candidate),(1 : Nat)) = _
      rw [← erase]
      rfl
    have hs := ProverCommitEntropy18.success (rawNext raw) 0 1 secret 15 drawn
    have hr : rawGenerate raw = .ok secret := congrArg Prod.fst hs
    rw [hr] at hz
    cases hz

/-- Sixteen-draw exhaustion is a subset of first-draw rejection. The actual
16-draw probability can be smaller; it is not silently set to zero. -/
theorem uniform_zero_mass :
    eventMass (fun raw : RawRand => rawGenerate raw = .error .repeatedZero) ≤ zeroBudget := by
  have sub := eventMass_mono
    (fun raw : RawRand => rawGenerate raw = .error .repeatedZero)
    (fun raw : RawRand => decode (raw 0) = none) zero_failure_first
  have coord : eventMass (fun raw : RawRand => decode (raw 0) = none) =
      eventMass (fun raw : Candidate => decode raw = none) := CommitReadsR1.mass_coord (N := 16) (X := Candidate) 0
        (fun r : Candidate => decode r = none)
  exact sub.trans (coord.trans_le candidate_bad_mass)

/-- Any specified per-attempt OS/zero masses admit this union bound, with no
independence assertion and no dropping rejected attempt histories. -/
theorem eight_failure_mass {M : Type} [Fintype M]
    (bad : Fin 8 → M → Prop) (δos δzero : ℚ)
    (per_attempt : ∀ i, eventMass (bad i) ≤ δos+δzero) :
    eventMass (fun m => ∃ i, bad i m) ≤ 8*(δos+δzero) := by
  simpa only [eventMass,R0Z.FsAbortBounds.mass,Fintype.card_fin,Nat.cast_ofNat] using
    R0Z.FsAbortBounds.mass_exists_le_card bad (δos+δzero) per_attempt

#print axioms bad_disjoint
#print axioms failure_mass
#print axioms always_os_mass
#print axioms no_universal_os_bound
#print axioms decode_none_iff
#print axioms candidate_bad_mass
#print axioms zero_failure_first
#print axioms uniform_zero_mass
#print axioms eight_failure_mass
end R1Z.ProverCommitEntropy34
