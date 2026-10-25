import R1Z.ProverRwEntropyAbort64

/-! Exact source-model exhaustion inclusion. Bounds are stated on their
explicit finite carrier; neither an OS law nor native adequacy is inferred. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwEntropyExhaust64
open R0Z.FsStatement R0Z.FsAbort R0Z.FsGood R0Z.HvzkV
open ProverCommitPublicNonce40 ProverCommitLedger36 ProverRwEntropyAbort64
attribute [local instance] Classical.propDecidable

theorem exhaustion_first (schedule : Schedule) (tape : Nat → Raw)
    (s : State) (fuel : Nat)
    (exhausted : (run schedule tape (fuel+1) s).1 = .error .repeatedZero) :
    decode (tape s.cursor) = none := by
  cases he : (ask schedule .rng s).1 with
  | error e =>
    simp only [run,ProverCommitPublicNonce40.next,he] at exhausted
    cases exhausted
  | ok u =>
    cases hd : decode (tape s.cursor) with
    | none => rfl
    | some secret =>
      simp only [run,ProverCommitPublicNonce40.next,he,hd] at exhausted
      cases exhausted

/-- A rejected public nonce costs no fill and cannot be hidden inside a
uniform-private-byte rejection estimate. -/
theorem zero_nonce_mass {R : Type} [Fintype R] [Nonempty R]
    (schedule : R → Schedule) (tape : R → Nat → Raw) (initial : R → State) :
    eventMass (zeroBad (fun _ => 0) schedule tape initial) = 1 := by
  simp [zeroBad,zero_guard,eventMass,mean_const]

abbrev Coins := Fin 16 → Raw
def tape (coins : Coins) (index : Nat) : Raw := coins (Fin.ofNat 16 index)

/-- Even a schedule correlated with the whole tape cannot turn a first good
candidate into repeated-zero exhaustion. Only the first coordinate is used
for this conservative bound; no claim of a sixteenth power is made. -/
theorem exhaustion_mass
    (nonce : Coins → Path) (admitted : ∀ coins, nonce coins ≠ 0)
    (schedule : Coins → Schedule) (initial : Coins → State)
    (cursor : ∀ coins, (initial coins).cursor = 0) :
    eventMass (zeroBad nonce schedule tape initial) ≤ zeroBudget := by
  have inclusion : ∀ coins, zeroBad nonce schedule tape initial coins →
      decode (coins 0) = none := by
    intro coins hz
    unfold zeroBad generate at hz
    rw [if_neg (admitted coins)] at hz
    have first := exhaustion_first (schedule coins) (tape coins) (initial coins) 15 hz
    simpa only [cursor coins,tape,Fin.ofNat_zero] using first
  have sub := R0Z.HvzkV.eventMass_mono
    (zeroBad nonce schedule tape initial) (fun coins : Coins => decode (coins 0) = none)
    inclusion
  have coord : eventMass (fun coins : Coins => decode (coins 0) = none) =
      eventMass (fun raw : Raw => decode raw = none) :=
    CommitReadsR1.mass_coord (N := 16) (X := Raw) 0 (fun raw => decode raw = none)
  exact sub.trans (coord.trans_le candidate_bad_mass)

#print axioms exhaustion_first
#print axioms zero_nonce_mass
#print axioms exhaustion_mass
end R1Z.ProverRwEntropyExhaust64
