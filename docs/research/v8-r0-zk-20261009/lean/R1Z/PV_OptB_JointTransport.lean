import R1Z.PV_OptB_OffBad
import R1Z.ProverCommitFuelJoin22
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_OptB_JointTransport
open R0Z R0Z.FsGood R0Z.FsAbort R0Z.HvzkV R0Z.FsStatement

/-- A reached failure uses the complete original observation carrier. The
successful branch and failure decoder are data; this does not install a new
simulator or remove side channels. -/
def overlay {Ω E V : Type} (signal : Ω → Option E) (normal : Ω → V) (failure : E → V) (r : Ω) : V :=
  match signal r with
  | none => normal r
  | some e => failure e

#print axioms overlay
theorem overlay_none {Ω E V : Type} (signal : Ω → Option E) (normal : Ω → V)
    (failure : E → V) (r : Ω) (h : signal r = none) : overlay signal normal failure r = normal r := by
  simp only [overlay,h]

#print axioms overlay_none
theorem overlay_some {Ω E V : Type} (signal : Ω → Option E) (normal : Ω → V)
    (failure : E → V) (r : Ω) (e : E) (h : signal r = some e) : overlay signal normal failure r = failure e := by
  simp only [overlay,h]

#print axioms overlay_some
theorem overlay_bounds {Ω E : Type} (signal : Ω → Option E) (normal : Ω → ℚ)
    (failure : E → ℚ) (hn : ∀ r, 0 ≤ normal r ∧ normal r ≤ 1)
    (hf : ∀ e, 0 ≤ failure e ∧ failure e ≤ 1) (r : Ω) :
    0 ≤ overlay signal normal failure r ∧ overlay signal normal failure r ≤ 1 := by
  unfold overlay
  cases signal r with
  | none => exact hn r
  | some e => exact hf e

#print axioms overlay_bounds
theorem overlay_agreement {Ω E V : Type} (leftSignal rightSignal : Ω → Option E)
    (left right : Ω → V) (failure : E → V) (r : Ω)
    (same : leftSignal r = rightSignal r)
    (success : leftSignal r = none → left r = right r) :
    overlay leftSignal left failure r = overlay rightSignal right failure r := by
  unfold overlay
  rw [← same]
  cases hs : leftSignal r with
  | none => exact success hs
  | some e => rfl

#print axioms overlay_agreement
theorem until_bad_overlay {Ω E : Type} [Fintype Ω]
    (leftSignal rightSignal : Ω → Option E) (left right : Ω → ℚ) (failure : E → ℚ)
    (bad : Ω → Prop)
    (hl : ∀ r, 0 ≤ left r ∧ left r ≤ 1) (hr : ∀ r, 0 ≤ right r ∧ right r ≤ 1)
    (hf : ∀ e, 0 ≤ failure e ∧ failure e ≤ 1)
    (same : ∀ r, ¬ bad r → leftSignal r = rightSignal r)
    (success : ∀ r, ¬ bad r → leftSignal r = none → left r = right r) :
    |mean (overlay leftSignal left failure) - mean (overlay rightSignal right failure)| ≤ eventMass bad := by
  exact until_bad _ _ (overlay_bounds leftSignal left failure hl hf)
    (overlay_bounds rightSignal right failure hr hf) bad
    (fun r good => overlay_agreement leftSignal rightSignal left right failure r (same r good) (success r good))

#print axioms until_bad_overlay
theorem same_bound_no_new_charge {Ω E : Type} [Fintype Ω]
    (leftSignal rightSignal : Ω → Option E) (left right : Ω → ℚ) (failure : E → ℚ)
    (bad : Ω → Prop) (ε : ℚ) (mass_bound : eventMass bad ≤ ε)
    (hl : ∀ r, 0 ≤ left r ∧ left r ≤ 1) (hr : ∀ r, 0 ≤ right r ∧ right r ≤ 1)
    (hf : ∀ e, 0 ≤ failure e ∧ failure e ≤ 1)
    (same : ∀ r, ¬ bad r → leftSignal r = rightSignal r)
    (success : ∀ r, ¬ bad r → leftSignal r = none → left r = right r) :
    |mean (overlay leftSignal left failure) - mean (overlay rightSignal right failure)| ≤ ε :=
  (until_bad_overlay leftSignal rightSignal left right failure bad hl hr hf same success).trans mass_bound

#print axioms same_bound_no_new_charge
theorem observe_overlay {Ω E V U : Type}
    (signal : Ω → Option E) (normal : Ω → V) (failure : E → V) (observe : V → U) :
    (fun r => observe (overlay signal normal failure r)) =
      overlay signal (fun r => observe (normal r)) (fun e => observe (failure e)) := by
  funext r
  unfold overlay
  cases signal r <;> rfl

#print axioms observe_overlay
/-- Replacement for the old RunJoin.agreement: require full equality only
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

#print axioms failure_run_join
theorem failure_test_bound {R M V E : Type}
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

#print axioms failure_test_bound
end R1Z.PV_OptB_JointTransport
