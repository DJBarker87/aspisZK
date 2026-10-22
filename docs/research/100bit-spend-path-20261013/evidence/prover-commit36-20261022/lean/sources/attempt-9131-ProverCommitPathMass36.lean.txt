import R1Z.ProverCommitLedger36
import R1Z.ProverCommitEnvironmentLaw35

/-! A uniform nonce does not imply a uniform deterministic hashed address.
This isolates the exact missing interface, without asserting that SHA-256
is constant or modifying any protocol hash assumption. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitPathMass36
open R0Z R0Z.FsStatement R0Z.FsAbort
open ProverCommitEntropy18 ProverCommitEnvironment35 ProverCommitEnvironmentLaw35
attribute [local instance] Classical.propDecidable

def pathMass (address : OracleAnswer → OracleAnswer) (entry : OracleAnswer) : ℚ :=
  eventMass (fun nonce => address nonce = entry)

/-- The exact E1 push-forward, before nonzero rejection. The source address
function stays inside the event; E1 does not remove it. -/
theorem E1_address {Context : Type} (law : Context → Candidate → ℚ)
    (rng : E1 law) (context : Context)
    (address : OracleAnswer → OracleAnswer) (entry : OracleAnswer) :
    conditionalMass law context (fun raw => address (raw 0) = entry) =
      pathMass address entry := by
  rw [E1_event law rng context]
  exact CommitReadsR1.mass_coord (N := 3) (X := OracleAnswer) 0
    (fun nonce => address nonce = entry)

theorem constant_address_mass (entry : OracleAnswer) :
    pathMass (fun _ => entry) entry = 1 := by
  simp [pathMass,eventMass,mean_const]

/-- Numerically false already for one adversarial entry and one raw draw.
This is a countermodel to an E1-only *generic* address theorem, not a claim
about the concrete SHA-256 function. -/
theorem no_E1_only_path_bound {Context : Type} (law : Context → Candidate → ℚ)
    (rng : E1 law) (context : Context) :
    ¬ ∀ (address : OracleAnswer → OracleAnswer) (entry : OracleAnswer),
      conditionalMass law context (fun raw => address (raw 0) = entry) ≤
        1 / (2 : ℚ)^256 := by
  intro bound
  have h := bound (fun _ => 0) 0
  rw [E1_address law rng context (fun _ => 0) 0,constant_address_mass] at h
  norm_num at h

/-- A permutation would suffice, but is an extra mathematical property of
the address function. No such property of native SHA-256 is assumed here. -/
theorem bijective_address_mass (address : OracleAnswer → OracleAnswer)
    (bijective : Function.Bijective address) (entry : OracleAnswer) :
    pathMass address entry = 1 / (2 : ℚ)^256 := by
  let e := Equiv.ofBijective address bijective
  have h := R0Z.FsAbortBounds.mass_equiv e (fun nonce => address nonce = entry)
  have point : (fun nonce => address (e.symm nonce) = entry) =
      (fun nonce => nonce = entry) := by
    funext nonce
    exact propext (by rw [show address (e.symm nonce) = nonce from e.apply_symm_apply nonce])
  change R0Z.FsAbortBounds.mass _ = _
  rw [h,point,R0Z.FsAbortBounds.mass_point,
    QueryScanSharedHistoryMass.answer_cardinality,Nat.cast_pow,Nat.cast_ofNat]

/-- The announced entry-count bound follows from a *separate* push-forward
bound. Entries may repeat; no independence among entry-hit events is used.
The hypothesis is exposed here precisely because E1 alone does not supply it. -/
theorem entries_bound {Context : Type} (law : Context → Candidate → ℚ)
    (rng : E1 law) (context : Context) (address : OracleAnswer → OracleAnswer)
    (entries : Nat) (entry : Fin entries → OracleAnswer) (δ : ℚ)
    (push_forward : ∀ p, pathMass address p ≤ δ) :
    conditionalMass law context (fun raw => ∃ i, address (raw 0) = entry i) ≤
      entries * δ := by
  rw [E1_event law rng context]
  change R0Z.FsAbortBounds.mass (fun raw : Candidate =>
    ∃ i, address (raw 0) = entry i) ≤ _
  rw [CommitReadsR1.mass_coord (N := 3) (X := OracleAnswer) 0
    (fun nonce => ∃ i, address nonce = entry i)]
  simpa only [eventMass,R0Z.FsAbortBounds.mass,Fintype.card_fin] using
    R0Z.FsAbortBounds.mass_exists_le_card
      (fun i : Fin entries => fun nonce => address nonce = entry i) δ
      (fun i => push_forward (entry i))

#print axioms E1_address
#print axioms constant_address_mass
#print axioms no_E1_only_path_bound
#print axioms bijective_address_mass
#print axioms entries_bound
end R1Z.ProverCommitPathMass36
