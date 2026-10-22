import R1Z.ProverCommitReservationGuess38
import R1Z.ProverCommitLedger36
import R1Z.ProverCommitFuelMass22

/-! D150's numerical conclusion requires a bound on adversarial ledger
entries. D148's actual ledger/schedule types contain no such bound. The
saturated ledger below is symbolic and never evaluated or enumerated. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitReservationScope38
open R0Z R0Z.FsStatement R0Z.FsAbort R0Z.FsGood R0Z.HvzkV
open GamesR1PBin ProverCommitReservationGuess38
attribute [local instance] Classical.propDecidable

/-- A finite, byte-blind initial ledger permitted by the D148 carrier.
This mathematical counterexample makes no physical storage claim. -/
def saturatedLedger : ProverCommitLedger36.Ledger :=
  (Finset.univ : Finset OracleAnswer).toList

theorem full_list_mem {U : Type} [Fintype U] [DecidableEq U] (path : U) :
    path ∈ (Finset.univ : Finset U).toList :=
  Finset.mem_toList.mpr (Finset.mem_univ path)

theorem saturated_mem (path : OracleAnswer) : path ∈ saturatedLedger :=
  full_list_mem path

theorem saturated_guess (queries : List (List UInt8)) (nonce : NZ)
    (path : OracleAnswer) : reservationGuess queries saturatedLedger nonce path :=
  Or.inr (saturated_mem path)

/-- This holds for every address function, including every fixed shared ROM;
E1/P1/E2 cannot make an already occupied path fresh. -/
theorem saturated_mass {R : Type} [Fintype R] [Nonempty R]
    (queries : R → List (List UInt8)) (nonce : R → NZ)
    (path : R → OracleAnswer) :
    eventMass (fun r => reservationGuess (queries r) saturatedLedger (nonce r) (path r)) = 1 := by
  have shape : (fun r => reservationGuess (queries r) saturatedLedger (nonce r) (path r)) =
      fun _ => True := by
    funext r
    exact propext ⟨fun _ => True.intro,fun _ => saturated_guess _ _ _⟩
  rw [shape]
  simp only [eventMass,if_true,mean_const]

theorem saturated_duplicate (schedule : ProverCommitLedger36.Schedule)
    (unix : Bool) (path : OracleAnswer) :
    (ProverCommitLedger36.reserve schedule unix path
      ⟨[],0,saturatedLedger⟩).1 =
      .error ProverCommitEnvironment35.ReservationError.duplicate :=
  ProverCommitLedger36.duplicate_path schedule unix path _ (saturated_mem path)

/-- Even the new standalone charge cannot have the requested uniform numeric
conclusion without restricting entries or proving a better coupling. -/
theorem no_unrestricted_numeric :
    ¬ ∀ entries : Nat, budget 0 entries 1 < 1 / (2 : ℚ)^100 := by
  intro h
  have bad := h (2^256 - 1)
  norm_num [budget] at bad

/-- Conditional arithmetic only: 128 allows all 16 draws in each of eight
attempts. No assertion that native selection creates 128 reservations. -/
theorem bounded_charge {q entries attempts : Nat}
    (hq : q ≤ 2^64) (he : entries ≤ 2^64) (ha : attempts ≤ 128) :
    budget q entries attempts ≤ 1 / (2 : ℚ)^180 := by
  unfold budget
  calc
    ((q : ℚ) + entries) * attempts / ((2 : ℚ)^256 - 1) ≤
        ((2 : ℚ)^64 + (2 : ℚ)^64) * 128 / ((2 : ℚ)^256 - 1) := by
      gcongr
      · exact_mod_cast hq
      · exact_mod_cast he
      · exact_mod_cast ha
    _ ≤ 1 / (2 : ℚ)^180 := by norm_num

/-- A quantified and explicitly conditional replacement numeric expression.
The bound on entries is NOT present in D148, so this does not establish the
requested every-schedule headline and is not installed as that endpoint. -/
theorem bounded_total {scan q entries attempts : Nat}
    (hs : scan ≤ 2^65) (hq : q ≤ 2^64) (he : entries ≤ 2^64)
    (ha : attempts ≤ 128) :
    1 / (2 : ℚ)^109 + 1 / (2 : ℚ)^137 + 1 / (2 : ℚ)^454 +
      QueryScanFreshUnion.freshBudget scan + 2 * ProverCommitSeedEvent19.budget q +
      2 * ProverCommitFuelMass22.charge + 2 * budget q entries attempts <
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
  have hr := (bounded_charge hq he ha).trans
    (QueryScanHistoryRealNumerics.dyadic_mono (by omega : 109 ≤ 180))
  have upper : 1 / (2 : ℚ)^109 + 1 / (2 : ℚ)^137 + 1 / (2 : ℚ)^454 +
      QueryScanFreshUnion.freshBudget scan + 2 * ProverCommitSeedEvent19.budget q +
      2 * ProverCommitFuelMass22.charge + 2 * budget q entries attempts ≤
        12 / (2 : ℚ)^109 := by
    have pos : 0 ≤ 1 / (2 : ℚ)^109 := by positivity
    linarith
  exact upper.trans_lt (by norm_num)

#print axioms full_list_mem
#print axioms saturated_mem
#print axioms saturated_guess
#print axioms saturated_mass
#print axioms saturated_duplicate
#print axioms no_unrestricted_numeric
#print axioms bounded_charge
#print axioms bounded_total
end R1Z.ProverCommitReservationScope38
