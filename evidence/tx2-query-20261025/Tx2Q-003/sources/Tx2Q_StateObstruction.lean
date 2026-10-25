import CheckpointBytes5Output
import OraclePortCheckpointResumeC5
set_option autoImplicit false
noncomputable section
namespace AspisR1.Tx2Q_StateObstruction
open AspisR1Stage2
abbrev K := OraclePortCheckpointAbiC5.K
abbrev E := OraclePortCheckpointAbiC5.E
attribute [local irreducible] OraclePortCheckpointStateC3.advance
  OraclePortCheckpointStateC3.write QueryAccumulator.run

/-- Symbolic induction, without evaluating a concrete recurrence. -/
theorem zero_power (m : OraclePortCheckpointStateC3.Prepared K E)
    (s : QueryAccumulator.State K E) (h : s.power = 0) (n : Nat) :
    (OraclePortCheckpointStateC3.advance m n s).power = 0 ∧
    (OraclePortCheckpointStateC3.advance m n s).rhs = s.rhs := by
  induction n with
  | zero => exact ⟨h,rfl⟩
  | succ n ih =>
    simp only [OraclePortCheckpointStateC3.advance,QueryAccumulator.step,ih.1,
      zero_mul,map_zero,add_zero,ih.2]
    trivial

theorem saved_power (data : MatchingSupport.Data E) (q : Fin 22 → Fin 262144) :
    (OraclePortCheckpointStateC3.write
      (OraclePortCheckpointResumeC5.model data 1 q)).accumulator.power = 1 := by
  unfold OraclePortCheckpointStateC3.write OraclePortCheckpointResumeC5.model
    OraclePortCheckpointStateC3.fromData
  rw [QueryAccumulator.run_power,one_pow]

theorem not_saved (a : verifier.Accumulator)
    (data : MatchingSupport.Data E) (q : Fin 22 → Fin 262144)
    (power : CheckpointBytes5Output.ofK a.power = 0) :
    CheckpointBytes5Output.accumulator a ≠
      (OraclePortCheckpointStateC3.write
        (OraclePortCheckpointResumeC5.model data 1 q)).accumulator := by
  intro same
  have h := congrArg QueryAccumulator.State.power same
  change CheckpointBytes5Output.ofK a.power = _ at h
  rw [power,saved_power] at h
  exact zero_ne_one h

theorem not_twelve (a saved : verifier.Accumulator)
    (data : MatchingSupport.Data E) (q : Fin 22 → Fin 262144)
    (power : CheckpointBytes5Output.ofK saved.power = 0)
    (rhs : CheckpointBytes5Output.ofE a.rhs ≠ CheckpointBytes5Output.ofE saved.rhs) :
    CheckpointBytes5Output.accumulator a ≠
      OraclePortCheckpointStateC3.advance (OraclePortCheckpointResumeC5.model data 1 q)
        12 (CheckpointBytes5Output.accumulator saved) := by
  intro same
  have h := congrArg QueryAccumulator.State.rhs same
  have retained := (zero_power (OraclePortCheckpointResumeC5.model data 1 q)
    (CheckpointBytes5Output.accumulator saved) power 12).2
  exact rhs (h.trans retained)

#print axioms zero_power
#print axioms saved_power
#print axioms not_saved
#print axioms not_twelve
end AspisR1.Tx2Q_StateObstruction
end
