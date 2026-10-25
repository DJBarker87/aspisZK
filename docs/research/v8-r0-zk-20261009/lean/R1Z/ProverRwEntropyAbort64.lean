import R1Z.ProverCommitPublicNonce40

/-! Abort accounting for the selected 64-byte model, not the historical
96-byte owner. The OS term remains exact. E1 specifies successful bytes;
it cannot supply availability or the missing native/effect association. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwEntropyAbort64
open R0Z.FsStatement R0Z.FsAbort R0Z.FsGood R0Z.HvzkV
open ProverCommitPublicNonce40 ProverCommitLedger36
attribute [local instance] Classical.propDecidable

def osBad {R : Type} (nonce : R → Path) (schedule : R → Schedule)
    (tape : R → Nat → Raw) (initial : R → State) (r : R) : Prop :=
  ∃ e, (generate (nonce r) (schedule r) (tape r) (initial r)).1 = .error (.os e)

def zeroBad {R : Type} (nonce : R → Path) (schedule : R → Schedule)
    (tape : R → Nat → Raw) (initial : R → State) (r : R) : Prop :=
  (generate (nonce r) (schedule r) (tape r) (initial r)).1 = .error .repeatedZero

def failed {R : Type} (nonce : R → Path) (schedule : R → Schedule)
    (tape : R → Nat → Raw) (initial : R → State) (r : R) : Prop :=
  ∃ e, (generate (nonce r) (schedule r) (tape r) (initial r)).1 = .error e

/-- This includes zero public nonce, adaptive state/tape selection, and every
OS-error history. No factorization of the finite law is required. -/
theorem failure_mass {R : Type} [Fintype R]
    (nonce : R → Path) (schedule : R → Schedule)
    (tape : R → Nat → Raw) (initial : R → State) :
    eventMass (failed nonce schedule tape initial) =
      eventMass (osBad nonce schedule tape initial) +
      eventMass (zeroBad nonce schedule tape initial) := by
  unfold eventMass
  rw [← R0Z.FsAbortBounds.mean_add'']
  congr 1
  funext r
  unfold failed osBad zeroBad
  cases (generate (nonce r) (schedule r) (tape r) (initial r)).1 with
  | ok secret => simp
  | error e => cases e <;> simp

theorem decode_none_iff (raw : Raw) :
    decode raw = none ↔ ∃ i, raw i = 0 := by
  unfold decode
  split
  next good => simp only [Option.some_ne_none, false_iff, not_exists]; exact good
  next bad =>
    simp only [true_iff]
    simpa only [not_forall,not_not] using bad

def zeroBudget : ℚ := 2 / (2 : ℚ)^256

/-- A single successful uniform 64-byte return has two 32-byte halves.
This is a union bound, with no independence between their zero events. -/
theorem candidate_bad_mass :
    eventMass (fun raw : Raw => decode raw = none) ≤ zeroBudget := by
  have h := R0Z.FsAbortBounds.mass_exists_le_card
    (fun i : Fin 2 => fun raw : Raw => raw i = 0) (1 / (2 : ℚ)^256)
    (fun i => by
      rw [CommitReadsR1.mass_coord (N := 2) (X := OracleAnswer) i
        (fun a : OracleAnswer => a = 0)]
      rw [R0Z.FsAbortBounds.mass_point,QueryScanSharedHistoryMass.answer_cardinality,
        Nat.cast_pow,Nat.cast_ofNat])
  have equal : (fun raw : Raw => decode raw = none) = fun raw => ∃ i, raw i = 0 :=
    funext fun raw => propext (decode_none_iff raw)
  rw [equal]
  simpa only [eventMass,R0Z.FsAbortBounds.mass,Fintype.card_fin,Nat.cast_ofNat,
    zeroBudget,div_eq_mul_inv,one_mul] using h

def unavailable : Schedule := fun _ _ _ => ⟨some 0,[]⟩

/-- The actual model records the failed RNG request and preserves its cursor
and ledger. The random tape is never read on this path. -/
theorem unavailable_generate (nonce : Path) (nonzero : nonce ≠ 0)
    (tape : Nat → Raw) (s : State) :
    generate nonce unavailable tape s =
      (.error (.os (.other 0)),
        {s with history := s.history ++ [(.rng,.error (.other 0))]}) := by
  have hn : ProverCommitPublicNonce40.next unavailable tape s =
      (.error (.other 0),{s with history := s.history ++ [(.rng,.error (.other 0))]}) := by
    simp only [ProverCommitPublicNonce40.next,ask,unavailable,inject,
      faultResult,record,List.append_nil]
  unfold generate
  rw [if_neg nonzero]
  exact run_os_error unavailable tape s _ (.other 0) 15 hn

theorem unavailable_mass {R : Type} [Fintype R] [Nonempty R]
    (nonce : R → Path) (nonzero : ∀ r, nonce r ≠ 0)
    (tape : R → Nat → Raw) (initial : R → State) :
    eventMass (osBad nonce (fun _ => unavailable) tape initial) = 1 := by
  unfold osBad
  simp only [unavailable_generate _ (nonzero _)]
  simp [eventMass,mean_const]

/-- E1 alone permits abort probability one, even for admitted nonzero public
nonces. This does not refute privacy or postulate an OS failure probability.
It identifies precisely why an availability bound cannot be inferred from E1. -/
theorem e1_no_subunit_availability (δ : ℚ) (small : δ < 1) :
    ∃ law : Unit → Raw → ℚ, E1 law ∧
      ¬ (∀ (nonce : Unit → Path), (∀ r, nonce r ≠ 0) →
        ∀ (schedule : Unit → Schedule) (tape : Unit → Nat → Raw)
          (initial : Unit → State), eventMass (osBad nonce schedule tape initial) ≤ δ) := by
  refine ⟨fun _ _ => 1 / (Fintype.card Raw : ℚ),fun _ _ => rfl,?_⟩
  intro bound
  have oneNonzero : (1 : Path) ≠ 0 := by
    intro eq
    have byte := congrFun eq 0
    exact (by decide : (1 : UInt8) ≠ 0) byte
  have h := bound (fun _ => 1) (fun _ => oneNonzero)
    (fun _ => unavailable) (fun _ _ _ => 0) (fun _ => ⟨[],0,[]⟩)
  rw [unavailable_mass _ (fun _ => oneNonzero)] at h
  exact (not_le_of_gt small) h

#print axioms failure_mass
#print axioms decode_none_iff
#print axioms candidate_bad_mass
#print axioms unavailable_generate
#print axioms unavailable_mass
#print axioms e1_no_subunit_availability
end R1Z.ProverRwEntropyAbort64
