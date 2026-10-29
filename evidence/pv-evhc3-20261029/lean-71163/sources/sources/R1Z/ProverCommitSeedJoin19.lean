import R1Z.ProverCommitSeedEvent19
/-! Seed-augmented whole observations and their explicit statistical loss. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitSeedJoin19
open R0Z R0Z.FsStatement R0Z.FsAbort R0Z.FsGood R0Z.HvzkV R0Z.LawTransport
open R1Z.ProverCommitSeedEvent19
attribute [local instance] Classical.propDecidable

structure RunJoin {R M V : Type} [Fintype R] [Fintype M]
    (runtime : R → V) (model : M → V)
    (bad : Fin 8 → M → Prop) (queries : M → List Entry) where
  cp : Coupling R (M × OracleAnswer)
  agreement : ∀ s, ¬ (∃ i, augmented bad queries i (cp.toM s)) →
    runtime (cp.toR s) = model (cp.toM s).1

theorem test_bound {R M V : Type} [Fintype R] [Fintype M] [Nonempty M]
    {runtime : R → V} {model : M → V} {bad : Fin 8 → M → Prop}
    {queries : M → List Entry} (join : RunJoin runtime model bad queries)
    (test : V → ℚ) (bounded : ∀ v, 0 ≤ test v ∧ test v ≤ 1)
    (q : Nat) (bound : ∀ m, (queries m).length ≤ q) :
    |mean (fun r => test (runtime r)) - mean (fun m => test (model m))| ≤
      eventMass (fun m => ∃ i, bad i m) + budget q := by
  have ht := until_bad
    (fun s => test (runtime (join.cp.toR s)))
    (fun s => test (model (join.cp.toM s).1))
    (fun s => bounded _) (fun s => bounded _)
    (fun s => ∃ i, augmented bad queries i (join.cp.toM s))
    (fun s hn => congrArg test (join.agreement s hn))
  have hr := join.cp.meanR (fun r => test (runtime r))
  have hi := join.cp.meanM (fun m => test (model m.1))
  have hp := R1Z.CouplingR1PBin.mp_fst (X := M) (Y := OracleAnswer)
    (fun m => test (model m))
  have hm := join.cp.meanM (fun m => if ∃ i, augmented bad queries i m then (1 : ℚ) else 0)
  have hmass : eventMass (fun s => ∃ i, augmented bad queries i (join.cp.toM s)) =
      eventMass (fun m => ∃ i, augmented bad queries i m) := by
    unfold eventMass
    convert hm using 1 <;> congr 1 <;> funext z <;> split_ifs <;> rfl
  rw [hr, hi, hp, hmass] at ht
  exact ht.trans (union_mass bad queries q bound)

/-- Product extension of an existing coupling retains both exact marginals. -/
def extend {R M : Type} [Fintype R] [Fintype M] (cp : Coupling R M) :
    Coupling R (M × OracleAnswer) where
  S := cp.S × OracleAnswer
  finS := inferInstance
  nonemptyS := inferInstance
  toR := fun s => cp.toR s.1
  toM := fun s => (cp.toM s.1, s.2)
  meanR := fun f => (R1Z.CouplingR1PBin.mp_fst (X := cp.S) (Y := OracleAnswer)
    (fun s => f (cp.toR s))).trans (cp.meanR f)
  meanM := by
    intro f
    rw [mean_product, mean_product]
    exact cp.meanM (fun m => mean (fun seed => f (m,seed)))

/-- Containment preserves every old whole-run certificate, with the seed
retained independently. It proves implication, not proper logical inclusion. -/
def of_old {R M V : Type} [Fintype R] [Fintype M]
    (runtime : R → V) (model : M → V) (old : Fin 8 → M → Prop)
    (queries : M → List Entry) (cp : Coupling R M)
    (agreement : ∀ s, ¬ (∃ i, old i (cp.toM s)) → runtime (cp.toR s) = model (cp.toM s)) :
    RunJoin runtime model old queries where
  cp := extend cp
  agreement := by
    intro s hn
    exact agreement s.1 (fun ⟨i, hi⟩ => hn ⟨i, Or.inl hi⟩)

theorem budget_pow64 : budget (2^64) = 1 / (2 : ℚ)^192 := by
  unfold budget
  rw [Nat.cast_pow, Nat.cast_ofNat, show (256 : Nat) = 64+192 from rfl, pow_add]
  field_simp

theorem total_lt_target {q r : Nat} (hq : q ≤ 2^65) (hr : r ≤ 2^64) :
    1 / (2 : ℚ)^109 + 1 / (2 : ℚ)^137 + 1 / (2 : ℚ)^454 +
      QueryScanFreshUnion.freshBudget q + 2 * budget r < 1 / (2 : ℚ)^100 := by
  have h137 := QueryScanHistoryRealNumerics.dyadic_mono (by omega : 109 ≤ 137)
  have h454 := QueryScanHistoryRealNumerics.dyadic_mono (by omega : 109 ≤ 454)
  have hf := QueryScanFreshNumerics.fresh_budget_small hq
  have hs : budget r ≤ 1 / (2 : ℚ)^109 :=
    (budget_mono hr).trans (by rw [budget_pow64]; exact
      QueryScanHistoryRealNumerics.dyadic_mono (by omega : 109 ≤ 192))
  have hsum : 1 / (2 : ℚ)^109 + 1 / (2 : ℚ)^137 + 1 / (2 : ℚ)^454 +
      QueryScanFreshUnion.freshBudget q + 2 * budget r ≤ 8 / (2 : ℚ)^109 := by
    have hp : 0 ≤ 1 / (2 : ℚ)^109 := by positivity
    linarith
  apply hsum.trans_lt
  have he : 8 / (2 : ℚ)^109 = 1 / (2 : ℚ)^106 := by
    rw [show (109 : Nat) = 106+3 from rfl, pow_add, show (2 : ℚ)^3 = 8 by norm_num]
    field_simp
  rw [he]
  exact one_div_lt_one_div_of_lt (by positivity)
    (pow_lt_pow_right₀ (by norm_num) (by omega : 100 < 106))

#print axioms test_bound
#print axioms extend
#print axioms of_old
#print axioms budget_pow64
#print axioms total_lt_target
end R1Z.ProverCommitSeedJoin19
