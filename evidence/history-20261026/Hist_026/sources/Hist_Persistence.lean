import Hist_TraceProtection
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hist_Persistence
open Aeneas Aeneas.Std Result Hist_Store

/-- The source-indexed runtime effect is exactly the existing ledger event. -/
theorem step_effect (ops : AdapterRw.Ops) (program : S2W_ExtractionBoundary.Program)
    (before after : Store) (event : S2X.AccountEvent)
    (step : Step ops program before event after) :
    byteLedger after = S2X.applyEvent (byteLedger before) event := by
  cases step with
  | rollback => rfl
  | second => rfl
  | foreign target caller value different authorized =>
    funext key
    by_cases same : key = target <;> simp [byteLedger,put,S2X.applyEvent,same]
  | first target e data saved loaded authorized accepted =>
    funext key
    by_cases same : key = target <;> simp [byteLedger,put,S2X.applyEvent,same,alloc.vec.Vec.deref]

theorem trace_effect (ops : AdapterRw.Ops) (program : S2W_ExtractionBoundary.Program)
    (before after : Store) (events : List S2X.AccountEvent)
    (trace : Trace ops program before events after) :
    byteLedger after = S2X.history (byteLedger before) events := by
  induction trace with
  | nil => rfl
  | cons step trace ih =>
    rw [S2X.history,← step_effect ops program _ _ _ step]
    exact ih

/-- Constructor with the REAL events and ledger. No protected-history field
is an input, and no empty history is manufactured. Runtime trace membership
still needs to be associated with a concrete deployed execution. -/
def binding (ops : AdapterRw.Ops) (program : S2W_ExtractionBoundary.Program)
    (before after : Store) (key : Nat) (events : List S2X.AccountEvent)
    (trace : Trace ops program before events after)
    (owner : (before key).owner = program)
    (initialized : Initialized (before key).data) :
    S2X.CheckpointVersionBinding (byteLedger before key) (byteLedger after key) where
  key := key
  ledger := byteLedger before
  events := events
  savedAtCommit := rfl
  loadedAtEntry := congrFun (trace_effect ops program before after events trace) key
  noInterveningWrite := (Hist_TraceProtection.trace_frame ops program before after key events trace owner initialized).1

theorem retained (ops : AdapterRw.Ops) (program : S2W_ExtractionBoundary.Program)
    (before after : Store) (key : Nat) (events : List S2X.AccountEvent)
    (trace : Trace ops program before events after)
    (owner : (before key).owner = program)
    (initialized : Initialized (before key).data) : byteLedger after key = byteLedger before key :=
  S2X.checkpoint_persistence _ _ (binding ops program before after key events trace owner initialized)

#print axioms step_effect
#print axioms trace_effect
#print axioms binding
#print axioms retained
end AspisR1.Hist_Persistence
end
