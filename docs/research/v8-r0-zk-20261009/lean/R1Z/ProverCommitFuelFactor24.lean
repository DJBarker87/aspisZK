import R1Z.ProverCommitFuelJoin22
import R1Z.ProverCommitEntropyJoin18
/-! The retained independent fuel tape cannot be manufactured as a function
of the already sampled model/seed. This rules out a tempting but invalid
construction of the requested source coupling; it does not refute existence
of a coupling using genuinely additional randomness. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitFuelFactor24
open R0Z R0Z.FsAbort R0Z.FsGood R0Z.HvzkV
attribute [local instance] Classical.propDecidable

/-- Exact product marginals exclude every deterministic graph when the
second factor has at least two elements, whatever the coupling space is. -/
theorem no_deterministic_factor {R X T : Type}
    [Fintype R] [Fintype X] [Fintype T] [Nonempty X] [Nontrivial T]
    (cp : Coupling R (X × T)) (choose : X → T) :
    ¬ (∀ s, (cp.toM s).2 = choose (cp.toM s).1) := by
  intro deterministic
  let x : X := Classical.choice inferInstance
  obtain ⟨t,different⟩ := exists_ne (choose x)
  have positive := ProverCommitEntropyJoin18.eventMass_pos_of_witness
    (fun p : X × T => p.2 ≠ choose p.1) (x,t) different
  have zero : eventMass (fun s : cp.S => (cp.toM s).2 ≠ choose (cp.toM s).1) = 0 := by
    simp only [eventMass,deterministic,ne_eq,not_true_eq_false,if_false,mean_const]
  have marginal := cp.meanM (fun p => if p.2 ≠ choose p.1 then (1 : ℚ) else 0)
  have masses : eventMass (fun s : cp.S => (cp.toM s).2 ≠ choose (cp.toM s).1) =
      eventMass (fun p : X × T => p.2 ≠ choose p.1) := by
    unfold eventMass
    convert marginal using 1 <;> congr 1 <;> funext p <;> split_ifs <;> rfl
  rw [zero] at masses
  exact (ne_of_gt positive) masses.symm

/-- The actual fuel carrier has two distinct constant tapes, without
enumerating any of its enormous finite function space. -/
theorem tape_nontrivial : Nontrivial ProverCommitFuelJoin22.Tape := by
  refine ⟨⟨(fun _ _ _ => 0),(fun _ _ _ => 1),?_⟩⟩
  intro same
  have eq := congrFun (congrFun (congrFun same ⟨0,by decide⟩) ⟨0,by decide⟩) ⟨0,by decide⟩
  exact (by decide : (0 : UInt8) ≠ 1) eq

/-- In a real RunJoin, even allowing dependence on the retained seed is
insufficient: its model marginal is the full independent product. -/
theorem runJoin_not_model_function {R M V : Type}
    [Fintype R] [Fintype M] [Nonempty M]
    {runtime : R → V} {model : M → V} {old : Fin 8 → M → Prop}
    {queries : M → List ProverCommitSeedEvent19.Entry}
    (join : ProverCommitFuelJoin22.RunJoin runtime model old queries)
    (choose : M × R0Z.FsStatement.OracleAnswer → ProverCommitFuelJoin22.Tape) :
    ¬ (∀ s, (join.cp.toM s).2 = choose (join.cp.toM s).1) := by
  letI := tape_nontrivial
  exact no_deterministic_factor join.cp choose

#print axioms no_deterministic_factor
#print axioms tape_nontrivial
#print axioms runJoin_not_model_function
end R1Z.ProverCommitFuelFactor24
