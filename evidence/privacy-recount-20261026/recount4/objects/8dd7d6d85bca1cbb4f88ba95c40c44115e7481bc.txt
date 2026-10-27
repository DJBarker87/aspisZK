import R1Z.QueryScanSharedHistoryMass
import R1Z.ProverCommitSimulatorOracle18
/-! One simulator-coin/shared-oracle component, not a final-game attack.
Even a perfectly uniform table gives a seeded hash coin a joint correlation
with a query at a guessed seed. Independent coin marginals do not discharge
this history boundary. Retry/accepted-view projection is not proved here. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitSimulatorSeedGuess18
open R0Z R0Z.FsAbort R0Z.FsGood R0Z.LawTransport
open R1Z.QueryScanSharedHistoryMass
attribute [local instance] Classical.propDecidable
variable {U : Type} [Fintype U] [Nonempty U]

/-- For fixed attempt/stream/counter, the source coin frames are also
injective in the seed. The shared-table seed-guess experiment below therefore
uses the same address relation, rather than a leaking invented experiment. -/
theorem seed_addresses_injective (attempt : Nat) (stream : UInt8) (counter : Nat) :
    Function.Injective (fun seed : R0Z.FsStatement.OracleAnswer =>
      ProverCommitSimulatorOracle18.address (List.ofFn seed) attempt stream counter) := by
  intro seed other same
  unfold ProverCommitSimulatorOracle18.address at same
  have h1 := List.append_cancel_right same
  have h2 := List.append_cancel_right h1
  have h3 := List.append_cancel_right h2
  have seeds := List.append_cancel_left h3
  simpa only [List.ofFn_inj] using seeds

/-- Two different entries of one uniform table coincide with mass 1/|U|. -/
theorem table_collision (a b : U) (different : a ≠ b) :
    eventMass (fun table : U → U => table a = table b) = 1 / (Fintype.card U : ℚ) := by
  unfold eventMass
  rw [R0Z.FsAbort.mean_equiv (R1Z.LazyTable.splitAt b)]
  have left (p : U × ({x : U // x ≠ b} → U)) :
      (R1Z.LazyTable.splitAt b).symm p a = p.2 ⟨a, different⟩ := by
    change (if h : a = b then p.1 else p.2 ⟨a, h⟩) = _
    rw [dif_neg different]
  have right (p : U × ({x : U // x ≠ b} → U)) :
      (R1Z.LazyTable.splitAt b).symm p b = p.1 := by
    change (if h : b = b then p.1 else p.2 ⟨b, h⟩) = _
    rw [dif_pos rfl]
  simp_rw [left, right]
  rw [mean_product]
  have inner (v : U) :
      mean (fun rest : {x : U // x ≠ b} → U =>
        if rest ⟨a, different⟩ = v then (1 : ℚ) else 0) = 1 / (Fintype.card U : ℚ) :=
    by simpa only [eventMass] using
      (eval_point_mass (A := {x : U // x ≠ b}) (U := U) ⟨a, different⟩ v)
  simp_rw [inner]
  exact mean_const _

/-- A source coin is H(seed), and one observer answer is H(guess).
Both use the same table, as HOST_HASH and programmed_hash's fallback do. -/
def observation (guess : U) (randomness : U × (U → U)) : U × U :=
  (randomness.2 randomness.1, randomness.2 guess)

def equalTest (pair : U × U) : ℚ := if pair.1 = pair.2 then 1 else 0

theorem independent_probability :
    mean (equalTest (U := U)) = 1 / (Fintype.card U : ℚ) := by
  unfold equalTest
  rw [mean_product]
  have inner (v : U) : mean (fun w : U => if v = w then (1 : ℚ) else 0) =
      1 / (Fintype.card U : ℚ) := by
    simpa only [eventMass, eq_comm (a := v)] using (point_mass v)
  simp_rw [inner]
  exact mean_const _

theorem seeded_probability (guess : U) :
    mean (fun r => equalTest (observation guess r)) =
      1 / (Fintype.card U : ℚ) +
        (1 - 1 / (Fintype.card U : ℚ)) / (Fintype.card U : ℚ) := by
  unfold observation equalTest
  rw [mean_product]
  let q : ℚ := 1 / (Fintype.card U : ℚ)
  have inner (seed : U) :
      mean (fun table : U → U => if table seed = table guess then (1 : ℚ) else 0) =
        if seed = guess then 1 else q := by
    by_cases same : seed = guess
    · subst seed
      simp only [if_pos rfl]
      exact mean_const 1
    · rw [if_neg same]
      simpa only [eventMass, q] using table_collision seed guess same
  simp_rw [inner]
  have decompose (seed : U) : (if seed = guess then (1 : ℚ) else q) =
      q + (if seed = guess then 1-q else 0) := by
    split <;> ring
  simp_rw [decompose]
  rw [mean_add', mean_const]
  congr 1
  simp only [mean, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rfl

/-- For 256-bit seeds/answers the one-query correlation exceeds the entire
8 × 2^-486 query-scan allowance. This is a component loss, not a 100-bit
privacy break and not a statement about the accepted final proof view. -/
theorem numerical_gap :
    (8 : ℚ) / 2^486 < (1 - 1 / (2 : ℚ)^256) / (2 : ℚ)^256 := by
  have two_le : (2 : ℚ) ≤ 2^256 := by
    have h := pow_le_pow_right₀ (by norm_num : (1 : ℚ) ≤ 2) (by omega : 1 ≤ 256)
    simpa only [pow_one] using h
  have qhalf : (1 : ℚ) / 2^256 ≤ 1/2 :=
    one_div_le_one_div_of_le (by norm_num) two_le
  have lower : (1 : ℚ) / 2^257 ≤ (1 - 1 / (2 : ℚ)^256) / (2 : ℚ)^256 := by
    calc
      _ = (1/2 : ℚ) / (2 : ℚ)^256 := by
        rw [show 257 = 256+1 from rfl, pow_succ]
        ring
      _ ≤ _ := div_le_div_of_nonneg_right (by linarith) (by positivity)
  have eight : (8 : ℚ) / 2^486 = 1 / (2 : ℚ)^483 := by
    rw [show 486 = 483+3 from rfl, pow_add, show (2 : ℚ)^3 = 8 by norm_num]
    ring
  rw [eight]
  apply lt_of_lt_of_le _ lower
  apply one_div_lt_one_div_of_lt (by positivity)
  exact pow_lt_pow_right₀ (by norm_num) (by omega : 257 < 483)

/-- No coupling of this precise coin/one-query component can give full
observation equality outside an event with only the query-scan budget. -/
theorem no_query_scan_only_join (size : Fintype.card U = 2^256) (guess : U) :
    ¬ ∃ (cp : Coupling (U × (U → U)) (U × U)) (bad : U × U → Prop),
      eventMass bad ≤ (8 : ℚ) / 2^486 ∧
      (∀ s, ¬ bad (cp.toM s) → observation guess (cp.toR s) = cp.toM s) := by
  rintro ⟨cp, bad, mass, agrees⟩
  have bounded (pair : U × U) : 0 ≤ equalTest pair ∧ equalTest pair ≤ 1 := by
    unfold equalTest
    split <;> norm_num
  have comparison := until_bad
    (fun s => equalTest (observation guess (cp.toR s)))
    (fun s => equalTest (cp.toM s))
    (fun s => bounded _) (fun s => bounded _)
    (fun s => bad (cp.toM s)) (fun s hn => congrArg equalTest (agrees s hn))
  have hm : eventMass (fun s => bad (cp.toM s)) = eventMass bad :=
    cp.meanM (fun m => if bad m then 1 else 0)
  have hr := cp.meanR (fun r => equalTest (observation guess r))
  have hi := cp.meanM (equalTest (U := U))
  rw [hr, hi, hm, seeded_probability, independent_probability] at comparison
  have gap : (8 : ℚ) / 2^486 <
      (1 - 1 / (Fintype.card U : ℚ)) / (Fintype.card U : ℚ) := by
    simpa only [size, Nat.cast_pow, Nat.cast_ofNat] using numerical_gap
  have positive : 0 < (1 - 1 / (Fintype.card U : ℚ)) / (Fintype.card U : ℚ) :=
    lt_trans (by positivity) gap
  have cancel (a b : ℚ) : a+b-a = b := by ring
  rw [cancel, abs_of_pos positive] at comparison
  exact (not_le_of_gt gap) (comparison.trans mass)

#print axioms seed_addresses_injective
#print axioms table_collision
#print axioms independent_probability
#print axioms seeded_probability
#print axioms numerical_gap
#print axioms no_query_scan_only_join
end R1Z.ProverCommitSimulatorSeedGuess18
