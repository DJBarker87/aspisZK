import OraclePortFrozen2Join

/-! Diagnostic only: Result/source identities do not determine an oracle
observation. This module is not a frozen-source counterexample, and supplies
no replacement premise to the soundness endpoint. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.VTop_ObservationBoundary
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open OraclePortStoredExperimentC4 OraclePortRuntimeBindingC7 OraclePortFrozen2Join

/-- Keep the complete returned value, including any source state, unchanged. -/
def extraRead {A : Type} (p : Program Bytes State A) : Program Bytes State A :=
  .ask [] (fun _ => p)

theorem extraRead_value {A : Type} (p : Program Bytes State A) (H : Bytes → State) :
    (eval H (extraRead p)).2 = (eval H p).2 := rfl

theorem extraRead_observation {A : Type} (p : Program Bytes State A) (H : Bytes → State) :
    eval H (extraRead p) ≠ eval H p := by
  intro same
  have lengths := congrArg (fun x => x.1.length) same
  simp only [extraRead, eval, List.length_cons] at lengths
  omega

/-- An arbitrary oracle program cannot be filled in by value-only extraction
premises. This witness intentionally exceeds the frozen verifier's budget. -/
def reads : Nat → Program Bytes State Bool
  | 0 => .done true
  | n+1 => .ask [] (fun _ => reads n)

theorem reads_value (n : Nat) (H : Bytes → State) : (eval H (reads n)).2 = true := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

theorem reads_length (n : Nat) (H : Bytes → State) : (eval H (reads n)).1.length = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [reads, eval, List.length_cons]
    omega

theorem no_unbound_verifier_join (D : LiteralByteProtocol.Decoder)
    (i : Input) (H : Bytes → State) :
    ¬ AcceptedRunJoin D (fun _ => reads 1162) := by
  intro join
  have same := join.verifier H i (reads_value 1162 H)
  have bound := verifier_budget D OraclePortFrozen2.dV_frozen2
    OraclePortFrozen2.decision_budget H i
  have lengths := congrArg (fun x => x.1.length) same
  rw [reads_length] at lengths
  omega

#print axioms extraRead_value
#print axioms extraRead_observation
#print axioms reads_value
#print axioms reads_length
#print axioms no_unbound_verifier_join
end AspisR1.VTop_ObservationBoundary
end
