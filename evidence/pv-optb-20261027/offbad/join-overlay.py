from step import append
m='R1Z/PV_OptB_JointTransport';ns='R1Z.PV_OptB_JointTransport'
append(m,ns,'failure_run_join','''/-- Replacement for the old RunJoin.agreement: require full equality only
on no-failure executions, plus joint reached-signal agreement on the same
coupling. This theorem does not discharge either native law. -/
def failure_run_join {R M V E : Type} [Fintype R] [Fintype M]
    (runtime : R → V) (model : M → V) (old : Fin 8 → M → Prop)
    (queries : M → List R1Z.ProverCommitSeedEvent19.Entry)
    (signalR : R → Option E) (signalM : M → Option E) (failure : E → V)
    (cp : Coupling R ((M × OracleAnswer) × R1Z.ProverCommitFuelJoin22.Tape))
    (signals : ∀ s, ¬ (∃ i, R1Z.ProverCommitFuelJoin22.bad old queries i (cp.toM s)) →
      signalR (cp.toR s) = signalM (cp.toM s).1.1)
    (success : ∀ s, ¬ (∃ i, R1Z.ProverCommitFuelJoin22.bad old queries i (cp.toM s)) →
      signalR (cp.toR s) = none → runtime (cp.toR s) = model (cp.toM s).1.1) :
    R1Z.ProverCommitFuelJoin22.RunJoin
      (overlay signalR runtime failure) (overlay signalM model failure) old queries where
  cp := cp
  agreement := by
    intro s good
    unfold overlay
    rw [← signals s good]
    cases hs : signalR (cp.toR s) with
    | none => exact success s good hs
    | some e => rfl
''')
append(m,ns,'failure_test_bound','''theorem failure_test_bound {R M V E : Type}
    [Fintype R] [Fintype M] [Nonempty M]
    (runtime : R → V) (model : M → V) (old : Fin 8 → M → Prop)
    (queries : M → List R1Z.ProverCommitSeedEvent19.Entry)
    (signalR : R → Option E) (signalM : M → Option E) (failure : E → V)
    (cp : Coupling R ((M × OracleAnswer) × R1Z.ProverCommitFuelJoin22.Tape))
    (signals : ∀ s, ¬ (∃ i, R1Z.ProverCommitFuelJoin22.bad old queries i (cp.toM s)) →
      signalR (cp.toR s) = signalM (cp.toM s).1.1)
    (success : ∀ s, ¬ (∃ i, R1Z.ProverCommitFuelJoin22.bad old queries i (cp.toM s)) →
      signalR (cp.toR s) = none → runtime (cp.toR s) = model (cp.toM s).1.1)
    (test : V → ℚ) (bounded : ∀ v, 0 ≤ test v ∧ test v ≤ 1)
    (q : Nat) (bound : ∀ m, (queries m).length ≤ q) :
    |mean (fun r => test (overlay signalR runtime failure r)) -
      mean (fun m => test (overlay signalM model failure m))| ≤
      eventMass (fun m => ∃ i, old i m) + R1Z.ProverCommitSeedEvent19.budget q +
        R1Z.ProverCommitFuelMass22.charge :=
  R1Z.ProverCommitFuelJoin22.test_bound
    (failure_run_join runtime model old queries signalR signalM failure cp signals success)
    test bounded q bound
''')
