import R1Z.QueryScanPrivacyFinal

/-! Exact separation of the existing handoff. Removing the mass field alone
is unsound: arbitrary all-True exceptions erase the execution agreement.
A usable execution-only join must instead name fixed model events. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.QueryScanHistorySplit
open R0Z.FsStatement R0Z.FsAbort R0Z.FsGood R0Z.HvzkV
  R1Z.QueryScanPrivacyFinal
attribute [local instance] Classical.propDecidable

/-- Literally ScanCoupling with only its probability field removed. -/
structure ScanExecution {R M : Type} [Fintype R] [Fintype M]
    (source : R → ℚ) (model : M → ℚ) where
  cp : Coupling R M
  queryScan : Fin 8 → cp.S → Prop
  R_wire_agreement_off_queryScan : ∀ s, ¬ (∃ i, queryScan i s) →
    source (cp.toR s) = model (cp.toM s)

def ScanExecution.ProbabilityContent {R M : Type} [Fintype R] [Fintype M]
    {f : R → ℚ} {g : M → ℚ} (e : ScanExecution f g) : Prop :=
  ∀ i, eventMass (e.queryScan i) ≤ scanProbability

def forget {R M : Type} [Fintype R] [Fintype M]
    {f : R → ℚ} {g : M → ℚ} (c : ScanCoupling f g) : ScanExecution f g :=
  ⟨c.cp, c.queryScan, c.R_wire_agreement_off_queryScan⟩

def complete {R M : Type} [Fintype R] [Fintype M]
    {f : R → ℚ} {g : M → ℚ} (e : ScanExecution f g)
    (p : e.ProbabilityContent) : ScanCoupling f g :=
  ⟨e.cp, e.queryScan, p, e.R_wire_agreement_off_queryScan⟩

theorem exact_split {R M : Type} [Fintype R] [Fintype M]
    (f : R → ℚ) (g : M → ℚ) :
    Nonempty (ScanCoupling f g) ↔ ∃ e : ScanExecution f g, e.ProbabilityContent := by
  constructor
  · rintro ⟨c⟩
    exact ⟨forget c, c.R_rom_query_word_history⟩
  · rintro ⟨e, p⟩
    exact ⟨complete e p⟩

/-- Every pair of observations admits an unbounded execution join whenever
its randomness carriers already admit a coupling. -/
def vacuousExecution {R M : Type} [Fintype R] [Fintype M]
    (f : R → ℚ) (g : M → ℚ) (cp : Coupling R M) : ScanExecution f g where
  cp := cp
  queryScan := fun _ _ => True
  R_wire_agreement_off_queryScan := by
    intro s hn
    exact False.elim (hn ⟨0, trivial⟩)

def unitCoupling : Coupling Unit Unit where
  S := Unit
  finS := inferInstance
  nonemptyS := inferInstance
  toR := id
  toM := id
  meanR := fun _ => rfl
  meanM := fun _ => rfl

theorem scanProbability_lt_one : scanProbability < 1 := by
  have h : (1 : ℚ) / 2^486 < 1 := by
    apply (div_lt_one (by positivity)).mpr
    exact one_lt_pow₀ (by norm_num) (by omega)
  exact scan_probability_le.trans_lt h

/-- A compiled Boolean-observation counterexample, not just a bad event
chosen for an otherwise correct coupling. No bounded coupling can exist. -/
theorem zero_one_no_scanCoupling :
    ¬ Nonempty (ScanCoupling (fun _ : Unit => (0 : ℚ)) (fun _ : Unit => (1 : ℚ))) := by
  rintro ⟨c⟩
  have h := scan_coupling_le _ _ c (fun _ => by norm_num) (fun _ => by norm_num)
  rw [mean_const, mean_const] at h
  have hsmall : (8 : ℚ) / 2^486 < 1 := by
    apply (div_lt_one (by positivity)).mpr
    have hh : (8 : ℚ) < 2^4 := by norm_num
    exact hh.trans_le (pow_le_pow_right₀ (by norm_num) (by omega : 4 ≤ 486))
  norm_num only [zero_sub, abs_neg, abs_one] at h
  linarith

theorem probability_not_execution_content :
    (∃ e : ScanExecution (fun _ : Unit => (0 : ℚ)) (fun _ : Unit => (1 : ℚ)),
      ¬ e.ProbabilityContent) ∧
    ¬ (∀ e : ScanExecution (fun _ : Unit => (0 : ℚ)) (fun _ : Unit => (1 : ℚ)),
      e.ProbabilityContent) := by
  have hn : ∀ e : ScanExecution (fun _ : Unit => (0 : ℚ)) (fun _ : Unit => (1 : ℚ)),
      ¬ e.ProbabilityContent := by
    intro e hp
    exact zero_one_no_scanCoupling ⟨complete e hp⟩
  let e := vacuousExecution (fun _ : Unit => (0 : ℚ)) (fun _ : Unit => (1 : ℚ)) unitCoupling
  exact ⟨⟨e, hn e⟩, fun hp => hn e (hp e)⟩

/-- The repair: exceptions are fixed model events, not arbitrary predicates
chosen by the source execution join. This structure has no mass fields. -/
structure ModelExecutionJoin {R M : Type} [Fintype R] [Fintype M]
    (source : R → ℚ) (model : M → ℚ) (bad : Fin 8 → M → Prop) where
  cp : Coupling R M
  agreement : ∀ s, ¬ (∃ i, bad i (cp.toM s)) → source (cp.toR s) = model (cp.toM s)

def ModelExecutionJoin.toScanCoupling {R M : Type} [Fintype R] [Fintype M]
    {f : R → ℚ} {g : M → ℚ} {bad : Fin 8 → M → Prop}
    (e : ModelExecutionJoin f g bad)
    (modelLaw : ∀ i, eventMass (bad i) ≤ scanProbability) : ScanCoupling f g where
  cp := e.cp
  queryScan := fun i s => bad i (e.cp.toM s)
  R_rom_query_word_history := by
    intro i
    have ht := e.cp.meanM (fun m => if bad i m then (1 : ℚ) else 0)
    exact ht.le.trans (modelLaw i)
  R_wire_agreement_off_queryScan := e.agreement

#print axioms exact_split
#print axioms scanProbability_lt_one
#print axioms zero_one_no_scanCoupling
#print axioms probability_not_execution_content
#print axioms ModelExecutionJoin.toScanCoupling
end R1Z.QueryScanHistorySplit
