import PV_MEAS_Coupling
import PV_MEAS_Finite

set_option autoImplicit false
noncomputable section
open MeasureTheory PV_MEAS_Law
namespace PV_MEAS_Fuel
open PV_MEAS_Average PV_MEAS_Uniform PV_MEAS_Finite PV_MEAS_Coupling
open R0Z R0Z.FsStatement R0Z.FsAbort R1Z
attribute [local instance] Classical.propDecidable

variable {R M V : Type} [MeasurableSpace R] [Fintype M] [Nonempty M]
    [MeasurableSpace M] [MeasurableSingletonClass M]
    [MeasurableSpace OracleAnswer] [MeasurableSingletonClass OracleAnswer]
    [MeasurableSpace ProverCommitFuelJoin22.Tape]
    [MeasurableSingletonClass ProverCommitFuelJoin22.Tape]

/-- The original fuel/seed/query bad event, transferred through an exact MODEL
marginal. The native and common carriers are arbitrary measured spaces. -/
theorem test_bound (μR : ProbabilityMeasure R)
    (cp : PV_MEAS_Coupling.Coupling μR
      (uniform ((M × OracleAnswer) × ProverCommitFuelJoin22.Tape)))
    (runtime : R → V) (model : M → V)
    (old : Fin 8 → M → Prop) (queries : M → List ProverCommitSeedEvent19.Entry)
    (test : V → ℚ) (bounded : ∀ v, 0 ≤ test v ∧ test v ≤ 1)
    (measurable_test : Measurable (fun r => (test (runtime r) : ℝ)))
    (agreement : ∀ s,
      ¬ (∃ i, ProverCommitFuelJoin22.bad old queries i (cp.toM s)) →
        runtime (cp.toR s) = model (cp.toM s).1.1)
    (q : Nat) (bound : ∀ m, (queries m).length ≤ q) :
    |(∫ₚ r, (test (runtime r) : ℝ) ∂(μR : Measure R)) -
      (mean (fun m => test (model m)) : ℝ)| ≤
      (eventMass (fun m => ∃ i, old i m) + ProverCommitSeedEvent19.budget q +
        ProverCommitFuelMass22.charge : ℚ) := by
  have ht := finite_model_bound μR cp (fun r => (test (runtime r) : ℝ))
    (fun m => (test (model m.1.1) : ℝ))
    (fun m => ∃ i, ProverCommitFuelJoin22.bad old queries i m)
    measurable_test (measurable_of_finite _) (measurable_of_finite _)
    (by intro r; exact ⟨by exact_mod_cast (bounded (runtime r)).1,
      by exact_mod_cast (bounded (runtime r)).2⟩)
    (by intro m; exact ⟨by exact_mod_cast (bounded (model m.1.1)).1,
      by exact_mod_cast (bounded (model m.1.1)).2⟩)
    (fun s hs => congrArg (fun v => (test v : ℝ)) (agreement s hs))
  rw [integral_rat_mean _ (fun m => (bounded (model m.1.1)).1)] at ht
  have hm : (∫ₚ m, (if ∃ i, ProverCommitFuelJoin22.bad old queries i m then (1 : ℝ) else 0)
      ∂(uniform ((M × OracleAnswer) × ProverCommitFuelJoin22.Tape) : Measure _)) =
      (eventMass (fun m => ∃ i, ProverCommitFuelJoin22.bad old queries i m) : ℝ) := by
    simpa only [eventMass, apply_ite, Rat.cast_one, Rat.cast_zero] using
      (integral_rat_mean (fun m => if ∃ i, ProverCommitFuelJoin22.bad old queries i m
        then (1 : ℚ) else 0) (by intro m; split_ifs <;> norm_num))
  rw [hm] at ht
  have hp : mean (fun m : (M × OracleAnswer) × ProverCommitFuelJoin22.Tape =>
      test (model m.1.1)) = mean (fun m => test (model m)) :=
    (CouplingR1PBin.mp_fst (X := M × OracleAnswer) (Y := ProverCommitFuelJoin22.Tape)
      (fun m => test (model m.1))).trans
      (CouplingR1PBin.mp_fst (X := M) (Y := OracleAnswer) (fun m => test (model m)))
  rw [hp] at ht
  exact ht.trans (by exact_mod_cast ProverCommitFuelJoin22.mass old queries q bound)

#print axioms test_bound
end PV_MEAS_Fuel
