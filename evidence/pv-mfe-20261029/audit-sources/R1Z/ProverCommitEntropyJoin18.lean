import R1Z.ProverCommitEntropy18
import R0Z.FsAbort
/-! Necessary conditions on an entropy adapter, not a replacement for a
whole-run certificate. All events and laws are explicit. Positive failure
mass alone does NOT refute a join outside the existing fixed bad events. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitEntropyJoin18
open R0Z R0Z.FsGood R0Z.FsAbort R1Z.ProverCommitEntropy18
attribute [local instance] Classical.propDecidable

/-- Any visible failure absent from the model must lie within the nominated
bad event, with its full probability. This applies to every observation type. -/
theorem failure_mass_le_bad {R M Obs : Type} [Fintype R] [Fintype M]
    (cp : Coupling R M) (runtime : R → Obs) (model : M → Obs)
    (bad : M → Prop) (failed : Obs → Prop)
    (agreement : ∀ s, ¬ bad (cp.toM s) → runtime (cp.toR s) = model (cp.toM s))
    (no_model_failure : ∀ m, ¬ failed (model m)) :
    eventMass (fun r => failed (runtime r)) ≤ eventMass bad := by
  unfold eventMass
  rw [← cp.meanR, ← cp.meanM]
  apply mean_le_mean
  intro s
  by_cases hb : bad (cp.toM s)
  · simp only [if_pos hb]
    split <;> norm_num
  · have hn : ¬ failed (runtime (cp.toR s)) := by
      rw [agreement s hb]
      exact no_model_failure _
    simp only [if_neg hb, if_neg hn, le_refl]

/-- Uniform finite draws give every possible failure trace positive mass.
The argument is symbolic and never enumerates a seed or trace space. -/
theorem eventMass_pos_of_witness {R : Type} [Fintype R] [Nonempty R]
    (event : R → Prop) (r : R) (hr : event r) : 0 < eventMass event := by
  unfold eventMass mean
  apply div_pos
  · have h : (1 : ℚ) ≤ ∑ x : R, if event x then (1 : ℚ) else 0 := by
      have one := Finset.single_le_sum (s := Finset.univ)
        (f := fun x : R => if event x then (1 : ℚ) else 0)
        (fun x _ => by split <;> norm_num) (Finset.mem_univ r)
      simpa only [if_pos hr] using one
    exact lt_of_lt_of_le (by norm_num) h
  · exact_mod_cast Fintype.card_pos

abbrev RawRand := Fin 16 → Candidate

def rawNext (raw : RawRand) (cursor : Nat) : Except Unit Candidate × Nat :=
  (.ok (raw ⟨cursor % 16, Nat.mod_lt _ (by decide)⟩), cursor+1)

def rawGenerate (raw : RawRand) : Except (Error Unit) R1Z.GamesR1PBin.SecP :=
  (generate (rawNext raw) 0).1

theorem zero_trace : rawGenerate (fun _ _ => 0) = .error .repeatedZero := by
  change (run (fun n : Nat =>
    ((.ok (fun _ => 0) : Except Unit Candidate), n+1)) 16 0).1 = _
  rw [zero_draws]

theorem raw_failure_positive :
    0 < eventMass (fun raw => rawGenerate raw = .error .repeatedZero) :=
  eventMass_pos_of_witness _ (fun _ _ => 0) zero_trace

/-- Consequently the unconditioned, bounded raw-draw sampler has no exact
coupling to an always-successful nonzero-secret carrier. A failure allowance,
conditioning, or an explicit transport bound is required at this component.
This says nothing about whether the fixed query-scan budget can absorb it. -/
theorem no_exact_success_coupling {M : Type} [Fintype M]
    (model : M → R1Z.GamesR1PBin.SecP) :
    ¬ ∃ cp : Coupling RawRand M,
      ∀ s, rawGenerate (cp.toR s) = Except.ok (model (cp.toM s)) := by
  rintro ⟨cp, agrees⟩
  have bound := failure_mass_le_bad cp rawGenerate (fun m => Except.ok (model m))
    (fun _ => False) (fun result => result = .error .repeatedZero)
    (fun s _ => agrees s) (fun _ => by intro h; cases h)
  have no_bad : eventMass (fun _ : M => False) = 0 := by
    simp only [eventMass, if_false, mean, Finset.sum_const_zero, zero_div]
  rw [no_bad] at bound
  exact (not_le_of_gt raw_failure_positive) bound

#print axioms failure_mass_le_bad
#print axioms eventMass_pos_of_witness
#print axioms zero_trace
#print axioms raw_failure_positive
#print axioms no_exact_success_coupling
end R1Z.ProverCommitEntropyJoin18
