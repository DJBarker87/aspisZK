import SCB_Replay
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCB_PhysicalRun
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open OraclePortStoredExperimentC4 OraclePortRuntimeBindingC7 OraclePortStoredAdmissionC4

/-- Retain exactly one chronological physical execution in the returned view.
The recorder is a ghost observer and issues no extra oracle requests. -/
def runtime (rust : Verifier) (P : Prover) : Runtime :=
  bind (OracleProgramRecording.record (originalWith rust (canon P)))
    (fun run => .done (some run))

theorem runtime_eval (rust : Verifier) (P : Prover) (H : Bytes → State) :
    eval H (runtime rust P) =
      ((eval H (originalWith rust (canon P))).1,
        some (eval H (originalWith rust (canon P)))) := by
  simp only [runtime,eval_bind,OracleProgramRecording.eval_record,eval,List.append_nil]

/-- L159 fails for a faithfully recorded single execution with an accepted,
nonempty verifier suffix. This does not assert a deployed source fixture. -/
theorem not_binding (D : LiteralByteProtocol.Decoder) (rust : Verifier)
    (physical : Port1_StoredCarrier.Physical rust) (P : Prover) (H : Bytes → State)
    (accepted : (eval H (originalWith rust (canon P))).2.2 = true)
    (nonempty : (eval H (rust (eval H (canon P)).2)).1 ≠ []) :
    ¬ StoredCarrierBinding D rust P (runtime rust P) := by
  intro binding
  have observed : (eval H (runtime rust P)).2 =
      some (eval H (originalWith rust (canon P))) := by rw [runtime_eval]
  exact SCB_Replay.not_single_run D rust physical (canon P) H nonempty
    (binding H _ observed accepted)

/-- A minimal non-vacuous model: one real oracle request and successful return.
It is a structural model, not the installed cryptographic implementation. -/
def oneQuery : Verifier := fun _ => .ask [] (fun _ => .done true)

theorem oneQuery_physical : Port1_StoredCarrier.Physical oneQuery := by
  intro i j pub stored
  rfl

theorem oneQuery_accepted (P : Prover) (H : Bytes → State) :
    (eval H (originalWith oneQuery (canon P))).2.2 = true := by
  rw [SCB_Replay.original_eval]
  rfl

theorem oneQuery_nonempty (P : Prover) (H : Bytes → State) :
    (eval H (oneQuery (eval H (canon P)).2)).1 ≠ [] := by
  exact List.cons_ne_nil _ _

theorem countermodel (D : LiteralByteProtocol.Decoder) (P : Prover) (H : Bytes → State) :
    (eval H (runtime oneQuery P)).2 =
      some (eval H (originalWith oneQuery (canon P))) ∧
    (eval H (originalWith oneQuery (canon P))).2.2 = true ∧
    ¬ StoredCarrierBinding D oneQuery P (runtime oneQuery P) :=
  ⟨by rw [runtime_eval],oneQuery_accepted P H,
    not_binding D oneQuery oneQuery_physical P H (oneQuery_accepted P H)
      (oneQuery_nonempty P H)⟩

#print axioms runtime_eval
#print axioms not_binding
#print axioms oneQuery_physical
#print axioms oneQuery_accepted
#print axioms oneQuery_nonempty
#print axioms countermodel
end AspisR1.SCB_PhysicalRun
end
