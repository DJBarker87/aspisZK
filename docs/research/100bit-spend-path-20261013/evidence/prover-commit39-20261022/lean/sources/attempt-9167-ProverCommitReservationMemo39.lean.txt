import R1Z.ProverCommitReservationGuess38
import R1Z.ProverCommitFuelMass22

/-! D151: only prior adversary memo queries are charged. Private ledger
membership is handled by exact coupling, not by this event. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitReservationMemo39
open R0Z R0Z.FsStatement R0Z.FsAbort R0Z.FsGood R0Z.HvzkV GamesR1PBin
open ProverCommitReservationRom37
local instance (priority := 10000) allDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p
local instance (priority := 10000) allDecEq (U : Type) : DecidableEq U := Classical.decEq U

abbrev Entry := ProverCommitSeedEvent19.Entry

def memoGuess (prior : List Entry) (nonce : NZ) : Prop :=
  reservationInput nonce.val ∈ prior.map Prod.fst

def budget (q attempts : Nat) : ℚ :=
  (q : ℚ) * attempts / ((2 : ℚ)^256 - 1)

theorem prior_mass (prior : List Entry) :
    eventMass (memoGuess prior) ≤ budget prior.length 1 := by
  unfold memoGuess budget
  convert ProverCommitReservationGuess38.query_list (prior.map Prod.fst) using 1 <;>
    simp only [List.length_map,Nat.cast_one,mul_one]

theorem budget_mono {q r a b : Nat} (hqr : q ≤ r) (hab : a ≤ b) :
    budget q a ≤ budget r b := by
  unfold budget
  gcongr

/-- The prior context can contain arbitrary earlier oracle answers, ledger
entries and schedule history. Its query list cannot depend on this new nonce.
This is a conditional fresh-draw calculation, not an independent-seed
replacement for the source's actual nonce. -/
theorem context_mass {C : Type} [Fintype C] [Nonempty C]
    (prior : C → List Entry) (q : Nat)
    (bound : ∀ c, (prior c).length ≤ q) :
    eventMass (fun r : C × NZ => memoGuess (prior r.1) r.2) ≤ budget q 1 := by
  unfold eventMass
  rw [R0Z.LawTransport.mean_product]
  have h := R0Z.FsGood.mean_le_mean
    (fun c => eventMass (memoGuess (prior c))) (fun _ => budget q 1)
    (fun c => (prior_mass (prior c)).trans (budget_mono (bound c) (le_refl _)))
  simpa only [eventMass,mean_const] using h

/-- Arbitrary dependence among attempts is allowed once the conditional
fresh-draw law has been transported to each actual reservation event. -/
theorem attempts_mass {M : Type} [Fintype M] [Nonempty M]
    (q attempts : Nat) (bad : Fin attempts → M → Prop)
    (per_attempt : ∀ i, eventMass (bad i) ≤ budget q 1) :
    eventMass (fun m => ∃ i, bad i m) ≤ budget q attempts := by
  have h := R0Z.FsAbortBounds.mass_exists_le_card bad (budget q 1) per_attempt
  rw [Fintype.card_fin] at h
  simpa only [R0Z.FsAbortBounds.mass,eventMass] using
    h.trans (le_of_eq (by unfold budget; ring))

attribute [-instance] allDecidable allDecEq
attribute [local instance] Classical.propDecidable

/-- 128 conservatively covers 16 raw draws per each of eight source attempts.
The source makes at most eight reservations, not 128. -/
theorem bounded_charge {q attempts : Nat} (hq : q ≤ 2^64) (ha : attempts ≤ 128) :
    budget q attempts ≤ 1 / (2 : ℚ)^180 := by
  exact (budget_mono hq ha).trans (by norm_num [budget])

theorem total_lt_target {scan q attempts : Nat}
    (hs : scan ≤ 2^65) (hq : q ≤ 2^64) (ha : attempts ≤ 128) :
    1 / (2 : ℚ)^109 + 1 / (2 : ℚ)^137 + 1 / (2 : ℚ)^454 +
      QueryScanFreshUnion.freshBudget scan + 2 * ProverCommitSeedEvent19.budget q +
      2 * ProverCommitFuelMass22.charge + 2 * budget q attempts <
        1 / (2 : ℚ)^100 := by
  have h137 := QueryScanHistoryRealNumerics.dyadic_mono (by omega : 109 ≤ 137)
  have h454 := QueryScanHistoryRealNumerics.dyadic_mono (by omega : 109 ≤ 454)
  have hf := QueryScanFreshNumerics.fresh_budget_small hs
  have hseed : ProverCommitSeedEvent19.budget q ≤ 1 / (2 : ℚ)^109 :=
    (ProverCommitSeedEvent19.budget_mono hq).trans (by
      rw [ProverCommitSeedJoin19.budget_pow64]
      exact QueryScanHistoryRealNumerics.dyadic_mono (by omega : 109 ≤ 192))
  have hc := ProverCommitFuelMass22.charge_le.trans
    (QueryScanHistoryRealNumerics.dyadic_mono (by omega : 109 ≤ 120))
  have hr := (bounded_charge hq ha).trans
    (QueryScanHistoryRealNumerics.dyadic_mono (by omega : 109 ≤ 180))
  have upper : 1 / (2 : ℚ)^109 + 1 / (2 : ℚ)^137 + 1 / (2 : ℚ)^454 +
      QueryScanFreshUnion.freshBudget scan + 2 * ProverCommitSeedEvent19.budget q +
      2 * ProverCommitFuelMass22.charge + 2 * budget q attempts ≤
        12 / (2 : ℚ)^109 := by
    have pos : 0 ≤ 1 / (2 : ℚ)^109 := by positivity
    linarith
  exact upper.trans_lt (by norm_num)

#print axioms prior_mass
#print axioms budget_mono
#print axioms context_mass
#print axioms attempts_mass
#print axioms bounded_charge
#print axioms total_lt_target
end R1Z.ProverCommitReservationMemo39
