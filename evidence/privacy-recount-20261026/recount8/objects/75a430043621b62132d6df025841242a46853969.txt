import R1Z.ProverCommitLedger36
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_LedgerHistory
open ProverCommitLedger36
open ProverCommitEnvironment35 (Kind Outcome)

theorem record_length (kind : Kind) (result : Outcome) (s : State) :
    (record kind result s).2.history.length = s.history.length + 1 := by
  simp only [record,List.length_append,List.length_singleton]

theorem inject_length (action : Action) (s : State) :
    (inject action s).history.length = s.history.length := rfl

theorem ask_length (schedule : Schedule) (kind : Kind) (s : State) :
    (ask schedule kind s).2.history.length = s.history.length + 1 := by
  exact record_length kind _ (inject _ s)

theorem create_length (path : Path) (action : Action) (s : State) :
    (createNew path action s).2.history.length = s.history.length + 1 := by
  by_cases member : path ∈ (inject action s).ledger
  · simpa only [createNew,member,if_true,inject_length] using
      record_length .create (.error .alreadyExists) (inject action s)
  · cases outcome : action.fault with
    | none =>
      simpa only [createNew,member,if_false,outcome,inject_length] using
        record_length .create (.ok ())
          ({inject action s with ledger := path :: (inject action s).ledger} : State)
    | some e =>
      simpa only [createNew,member,if_false,outcome,inject_length] using
        record_length .create (.error (.other e)) (inject action s)

theorem chain_length_ge (schedule : Schedule) (kinds : List Kind) (s : State) :
    s.history.length ≤ (ioChain schedule kinds s).2.history.length := by
  induction kinds generalizing s with
  | nil => exact Nat.le_refl _
  | cons kind rest ih =>
    have step := ask_length schedule kind s
    cases outcome : (ask schedule kind s).1 with
    | error e =>
      simp only [ioChain,outcome]
      omega
    | ok value =>
      simp only [ioChain,outcome]
      exact (Nat.le_of_lt (by omega : s.history.length < (ask schedule kind s).2.history.length)).trans (ih _)

#print axioms create_length
#print axioms chain_length_ge

#print axioms record_length
#print axioms inject_length
#print axioms ask_length
end R1Z.PV_RunJoin_LedgerHistory
