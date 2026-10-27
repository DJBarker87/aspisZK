import Port1_StoredCarrier
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCB_Replay
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open OraclePortStoredExperimentC4 OraclePortRuntimeBindingC7

theorem original_eval (rust : Verifier) (P : Prover) (H : Bytes → State) :
    eval H (originalWith rust P) =
      ((eval H P).1 ++ (eval H (rust (eval H P).2)).1,
        ((eval H P).2,(eval H (rust (eval H P).2)).2)) := by
  simp only [originalWith,eval_bind,eval,List.append_nil]

theorem physical_enrich (rust : Verifier) (physical : Port1_StoredCarrier.Physical rust)
    (w : CanonicalCutEnrichedTranscript.Words) (i : Input) :
    rust (enrich w i) = rust i := physical _ _ rfl rfl

/-- Annotation issues a second verifier evaluation. This is chronological log
equality, rather than distinct-address or acceptance equivalence. -/
theorem annotated_eval (D : LiteralByteProtocol.Decoder) (rust : Verifier)
    (physical : Port1_StoredCarrier.Physical rust) (P : Prover) (H : Bytes → State) :
    eval H (annotatedWith D rust P) =
      let v := eval H (originalWith rust P)
      (v.1 ++ (eval H (rust v.2.1)).1,
        (enrich (OraclePortStoredAdmissionC4.build D (view v)) v.2.1,v.2.2)) := by
  simp only [annotatedWith,original_eval,eval_bind,
    OracleProgramRecording.eval_record,eval,List.append_nil]
  rw [physical_enrich rust physical]

/-- A nonempty verifier suffix prevents the physical single execution's
RunView from being literally the compiler's replay-annotated RunView. -/
theorem not_single_run (D : LiteralByteProtocol.Decoder) (rust : Verifier)
    (physical : Port1_StoredCarrier.Physical rust) (P : Prover) (H : Bytes → State)
    (nonempty : (eval H (rust (eval H P).2)).1 ≠ []) :
    eval H (originalWith rust P) ≠ eval H (annotatedWith D rust P) := by
  intro same
  have lengths := congrArg (fun v : RunView => v.1.length) same
  rw [annotated_eval D rust physical P H,original_eval] at lengths
  simp only [List.length_append] at lengths
  have zero : (eval H (rust (eval H P).2)).1.length = 0 := by omega
  cases log : (eval H (rust (eval H P).2)).1 with
  | nil => exact nonempty log
  | cons head tail => simp only [log,List.length_cons] at zero; omega

#print axioms original_eval
#print axioms physical_enrich
#print axioms annotated_eval
#print axioms not_single_run
end AspisR1.SCB_Replay
end
