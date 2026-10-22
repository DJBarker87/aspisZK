import R1Z.ProverCommitReservationMemo39

/-! D152 raw seed memo event. The public nonce and arbitrary earlier answers
belong to the context, not to the private coordinate. All raw candidates are
charged before nonzero selection; there is no conditioning on success. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitPrivateMemo40
open R0Z R0Z.FsStatement R0Z.FsAbort R0Z.FsGood R0Z.HvzkV
attribute [local instance] Classical.propDecidable
abbrev Entry := ProverCommitSeedEvent19.Entry

def point (input : List UInt8) (seed : OracleAnswer) : Prop :=
  input.drop (input.length - 32) = List.ofFn seed

theorem point_unique (input : List UInt8) {s t : OracleAnswer}
    (hs : point input s) (ht : point input t) : s = t := by
  simpa only [List.ofFn_inj] using hs.symm.trans ht

/-- Covers both raw field-seed derivation domains and all private leaf salts,
regardless of the public prefix, nonce or statement length. -/
theorem source_suffix (frame : List UInt8) (seed : OracleAnswer) :
    point (frame ++ List.ofFn seed) seed := by
  simp [point]

def guessed (prior : List Entry) (seed : OracleAnswer) : Prop :=
  ∃ entry ∈ prior, point entry.1 seed

def budget (q attempts : Nat) : ℚ := (q : ℚ) * attempts / (2 : ℚ)^256

theorem point_mass (input : List UInt8) :
    eventMass (point input) ≤ 1 / (2 : ℚ)^256 := by
  by_cases exists_seed : ∃ s, point input s
  · obtain ⟨s,hs⟩ := exists_seed
    have hm := eventMass_mono (point input) (fun t => t = s)
      (fun t ht => point_unique input ht hs)
    rw [QueryScanSharedHistoryMass.point_mass, QueryScanSharedHistoryMass.answer_cardinality,
      Nat.cast_pow,Nat.cast_ofNat] at hm
    exact hm
  · have empty : point input = fun _ => False := by
      funext s
      exact propext ⟨fun hs => exists_seed ⟨s,hs⟩,False.elim⟩
    rw [empty]
    simp only [eventMass,if_false,mean_const]
    positivity

theorem list_mass (prior : List Entry) :
    eventMass (guessed prior) ≤ budget prior.length 1 := by
  induction prior with
  | nil => simp [guessed,eventMass,mean_const,budget]
  | cons a tail ih =>
    have shape : guessed (a::tail) = fun s => point a.1 s ∨ guessed tail s := by
      funext s
      simp only [guessed,List.mem_cons,exists_eq_or_imp]
    rw [shape]
    exact ((R0Z.FsAbortBounds.mass_or_le _ _).trans
      (add_le_add (point_mass a.1) ih)).trans (le_of_eq (by
        simp only [budget,List.length_cons,Nat.cast_add,Nat.cast_one]; ring))

theorem budget_mono {q r a b : Nat} (hqr : q ≤ r) (hab : a ≤ b) :
    budget q a ≤ budget r b := by
  unfold budget
  gcongr

/-- A context may contain the adversary's nonce selection after its earlier
queries. It may not contain this fresh successful raw OS coordinate. This
is the E1 product calculation, not a whole adaptive-experiment join. -/
theorem context_mass {C : Type} [Fintype C] [Nonempty C]
    (prior : C → List Entry) (q : Nat) (bound : ∀ c, (prior c).length ≤ q) :
    eventMass (fun r : C × OracleAnswer => guessed (prior r.1) r.2) ≤ budget q 1 := by
  unfold eventMass
  rw [R0Z.LawTransport.mean_product]
  have h := R0Z.FsGood.mean_le_mean
    (fun c => eventMass (guessed (prior c))) (fun _ => budget q 1)
    (fun c => (list_mass (prior c)).trans (budget_mono (bound c) (le_refl _)))
  simpa only [eventMass,mean_const] using h

/-- Union bound requires no independence among attempts. The conditional
coordinate law must still be proved for each actual execution event. -/
theorem attempts_mass {M : Type} [Fintype M] [Nonempty M]
    (q attempts : Nat) (bad : Fin attempts → M → Prop)
    (per_attempt : ∀ i, eventMass (bad i) ≤ budget q 1) :
    eventMass (fun m => ∃ i, bad i m) ≤ budget q attempts := by
  have h := R0Z.FsAbortBounds.mass_exists_le_card bad (budget q 1) per_attempt
  rw [Fintype.card_fin] at h
  simpa only [R0Z.FsAbortBounds.mass,eventMass] using
    h.trans (le_of_eq (by unfold budget; ring))

/-- Two raw seeds, two worlds; 128 is 16 candidates times eight attempts.
This is a raw-draw envelope, not 128 successful source reservations. -/
theorem bounded_charge {q attempts : Nat} (hq : q ≤ 2^64) (ha : attempts ≤ 128) :
    budget q attempts ≤ 1 / (2 : ℚ)^185 :=
  (budget_mono hq ha).trans (by norm_num [budget])

theorem total_lt_target {scan q attempts : Nat}
    (hs : scan ≤ 2^65) (hq : q ≤ 2^64) (ha : attempts ≤ 128) :
    1 / (2 : ℚ)^109 + 1 / (2 : ℚ)^137 + 1 / (2 : ℚ)^454 +
      QueryScanFreshUnion.freshBudget scan + 2 * ProverCommitSeedEvent19.budget q +
      2 * ProverCommitFuelMass22.charge + 4 * budget q attempts <
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
    (QueryScanHistoryRealNumerics.dyadic_mono (by omega : 109 ≤ 185))
  have upper : 1 / (2 : ℚ)^109 + 1 / (2 : ℚ)^137 + 1 / (2 : ℚ)^454 +
      QueryScanFreshUnion.freshBudget scan + 2 * ProverCommitSeedEvent19.budget q +
      2 * ProverCommitFuelMass22.charge + 4 * budget q attempts ≤
        16 / (2 : ℚ)^109 := by
    have pos : 0 ≤ 1 / (2 : ℚ)^109 := by positivity
    linarith
  exact upper.trans_lt (by norm_num)

#print axioms point_unique
#print axioms source_suffix
#print axioms point_mass
#print axioms list_mass
#print axioms budget_mono
#print axioms context_mass
#print axioms attempts_mass
#print axioms bounded_charge
#print axioms total_lt_target
end R1Z.ProverCommitPrivateMemo40
