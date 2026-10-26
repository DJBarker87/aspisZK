import R1Z.ProverCommitFuelMass22
/-! Fixed fuel exceptions on retained uniform coin coordinates. This does
not assert that a concrete implementation has the required coupling. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitFuelJoin22
open R0Z R0Z.FsStatement R0Z.FsAbort R0Z.FsGood R0Z.HvzkV R0Z.LawTransport
open ProverCommitFuelMass22
attribute [local instance] Classical.propDecidable
abbrev Tape := Fin count → Fin k → OracleAnswer

def failure (i : Fin count) (t : Tape) : Prop := exhausted (fun _ => 0) (t i)

theorem failure_mass (i : Fin count) : eventMass (failure i) ≤ 1 / (p : ℚ)^k := by
  have hm := QueryScanSharedHistoryMass.eval_uniform (U := Fin k → OracleAnswer) i
    (fun draws => if exhausted (fun _ => 0) draws then (1 : ℚ) else 0)
  change eventMass (failure i) = eventMass (exhausted (fun _ => (0 : UInt8))) at hm
  rw [exhaustion_mass,QueryScanSharedHistoryMass.answer_cardinality,Nat.cast_pow,Nat.cast_ofNat] at hm
  rw [hm]
  have hp : (0 : ℚ) < (p : ℚ) := by norm_num [p]
  apply one_div_le_one_div_of_le (pow_pos hp _)
  exact pow_le_pow_left₀ hp.le (show (p : ℚ) ≤ (2 : ℚ)^256 by norm_num [p]) k

def bad {M : Type} (old : Fin 8 → M → Prop)
    (queries : M → List ProverCommitSeedEvent19.Entry)
    (i : Fin 8) (r : (M × OracleAnswer) × Tape) : Prop :=
  ProverCommitSeedEvent19.augmented old queries i r.1 ∨
    (i = 0 ∧ ∃ j, failure j r.2)

theorem old_contained {M : Type} (old : Fin 8 → M → Prop)
    (queries : M → List ProverCommitSeedEvent19.Entry) (i : Fin 8)
    (r : (M × OracleAnswer) × Tape)
    (h : ProverCommitSeedEvent19.augmented old queries i r.1) : bad old queries i r := Or.inl h

theorem mass {M : Type} [Fintype M] [Nonempty M]
    (old : Fin 8 → M → Prop) (queries : M → List ProverCommitSeedEvent19.Entry)
    (q : Nat) (bound : ∀ m, (queries m).length ≤ q) :
    eventMass (fun r => ∃ i, bad old queries i r) ≤
      eventMass (fun m => ∃ i, old i m) + ProverCommitSeedEvent19.budget q + charge := by
  have sub : ∀ r, (∃ i, bad old queries i r) →
      (∃ i, ProverCommitSeedEvent19.augmented old queries i r.1) ∨ ∃ j, failure j r.2 := by
    rintro r ⟨i,ho | ⟨_,hf⟩⟩
    · exact Or.inl ⟨i,ho⟩
    · exact Or.inr hf
  have h := ((eventMass_mono _ _ sub).trans (R0Z.FsAbortBounds.mass_or_le _ _))
  have hleft : eventMass (fun r : (M × OracleAnswer) × Tape =>
      ∃ i, ProverCommitSeedEvent19.augmented old queries i r.1) =
      eventMass (fun r => ∃ i, ProverCommitSeedEvent19.augmented old queries i r) := by
    unfold eventMass
    convert R1Z.CouplingR1PBin.mp_fst (X := M × OracleAnswer) (Y := Tape)
      (fun r => if ∃ i, ProverCommitSeedEvent19.augmented old queries i r then (1 : ℚ) else 0) using 1 <;>
      congr 1 <;> funext r <;> split_ifs <;> rfl
  have hright : eventMass (fun r : (M × OracleAnswer) × Tape => ∃ j, failure j r.2) =
      eventMass (fun t => ∃ j, failure j t) := by
    unfold eventMass
    convert R1Z.CouplingR1PBin.mp_snd (X := M × OracleAnswer) (Y := Tape)
      (fun t => if ∃ j, failure j t then (1 : ℚ) else 0) using 1 <;>
      congr 1 <;> funext r <;> split_ifs <;> rfl
  have hc : eventMass (fun r => ∃ i, bad old queries i r) ≤
      eventMass (fun r : (M × OracleAnswer) × Tape =>
        ∃ i, ProverCommitSeedEvent19.augmented old queries i r.1) +
      eventMass (fun r : (M × OracleAnswer) × Tape => ∃ j, failure j r.2) := by
    simpa only [eventMass,R0Z.FsAbortBounds.mass] using h
  rw [hleft,hright] at hc
  exact hc.trans (add_le_add (ProverCommitSeedEvent19.union_mass old queries q bound)
    (union_bound failure failure_mass))

structure RunJoin {R M V : Type} [Fintype R] [Fintype M]
    (runtime : R → V) (model : M → V) (old : Fin 8 → M → Prop)
    (queries : M → List ProverCommitSeedEvent19.Entry) where
  cp : Coupling R ((M × OracleAnswer) × Tape)
  agreement : ∀ s, ¬ (∃ i, bad old queries i (cp.toM s)) →
    runtime (cp.toR s) = model (cp.toM s).1.1

theorem test_bound {R M V : Type} [Fintype R] [Fintype M] [Nonempty M]
    {runtime : R → V} {model : M → V} {old : Fin 8 → M → Prop}
    {queries : M → List ProverCommitSeedEvent19.Entry}
    (join : RunJoin runtime model old queries) (test : V → ℚ)
    (bounded : ∀ v, 0 ≤ test v ∧ test v ≤ 1)
    (q : Nat) (bound : ∀ m, (queries m).length ≤ q) :
    |mean (fun r => test (runtime r)) - mean (fun m => test (model m))| ≤
      eventMass (fun m => ∃ i, old i m) + ProverCommitSeedEvent19.budget q + charge := by
  have ht := until_bad (fun s => test (runtime (join.cp.toR s)))
    (fun s => test (model (join.cp.toM s).1.1))
    (fun s => bounded _) (fun s => bounded _)
    (fun s => ∃ i, bad old queries i (join.cp.toM s))
    (fun s hn => congrArg test (join.agreement s hn))
  have hm := join.cp.meanM (fun m => if ∃ i, bad old queries i m then (1 : ℚ) else 0)
  have hmass : eventMass (fun s => ∃ i, bad old queries i (join.cp.toM s)) =
      eventMass (fun m => ∃ i, bad old queries i m) := by
    unfold eventMass
    convert hm using 1 <;> congr 1 <;> funext z <;> split_ifs <;> rfl
  have hr := join.cp.meanR (fun r => test (runtime r))
  have hi := join.cp.meanM (fun m => test (model m.1.1))
  rw [hr,hi] at ht
  have hp : mean (fun m : (M × OracleAnswer) × Tape => test (model m.1.1)) =
      mean (fun m => test (model m)) :=
    (R1Z.CouplingR1PBin.mp_fst (X := M × OracleAnswer) (Y := Tape)
      (fun m => test (model m.1))).trans
    (R1Z.CouplingR1PBin.mp_fst (X := M) (Y := OracleAnswer) (fun m => test (model m)))
  rw [hp,hmass] at ht
  exact ht.trans (mass old queries q bound)

/-- Every old seed-augmented run certificate remains sufficient. Both exact
marginals are retained; the extra tape does not alter the model output. -/
def of_seed {R M V : Type} [Fintype R] [Fintype M]
    {runtime : R → V} {model : M → V} {old : Fin 8 → M → Prop}
    {queries : M → List ProverCommitSeedEvent19.Entry}
    (join : ProverCommitSeedJoin19.RunJoin runtime model old queries) :
    RunJoin runtime model old queries where
  cp := {
    S := join.cp.S × Tape
    finS := inferInstance
    nonemptyS := inferInstance
    toR := fun s => join.cp.toR s.1
    toM := fun s => (join.cp.toM s.1,s.2)
    meanR := fun f => (R1Z.CouplingR1PBin.mp_fst
      (X := join.cp.S) (Y := Tape) (fun s => f (join.cp.toR s))).trans (join.cp.meanR f)
    meanM := by
      intro f
      rw [mean_product,mean_product]
      exact join.cp.meanM (fun m => mean (fun t => f (m,t))) }
  agreement := by
    intro s hn
    exact join.agreement s.1 (fun ⟨i,hi⟩ => hn ⟨i,Or.inl hi⟩)

#print axioms of_seed

#print axioms failure_mass
#print axioms old_contained
#print axioms mass
#print axioms test_bound
end R1Z.ProverCommitFuelJoin22
