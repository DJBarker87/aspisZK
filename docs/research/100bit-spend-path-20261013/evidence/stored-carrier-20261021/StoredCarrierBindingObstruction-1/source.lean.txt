import OraclePortHeadlineFrozenPerAttempt

/-! The deployed-runtime parameter has no source semantics in the endpoint.
Same stored bytes do not determine its designated chronological observation. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.StoredCarrierBindingObstruction
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open OraclePortStoredExperimentC4 OraclePortRuntimeBindingC7

/-- Two accepting observations can carry identical inputs and differ only
in their logs. At least one violates the original runtime premise, whatever
source verifier, decoder and prover are selected. No hash collision is used. -/
theorem same_bytes_insufficient (D : LiteralByteProtocol.Decoder) (rust : Verifier)
    (P : Prover) (i : Input) (state : State) :
    ∃ (runtime : Runtime) (run : RunView),
      runtime = .done (some run) ∧ run.2.1 = i ∧ run.2.2 = true ∧
        ¬ StoredCarrierBinding D rust P runtime := by
  let r0 : RunView := ([], (i, true))
  let r1 : RunView := ([([],state)], (i, true))
  by_cases h0 : StoredCarrierBinding D rust P (.done (some r0))
  · refine ⟨.done (some r1), r1, rfl, rfl, rfl, ?_⟩
    intro h1
    have e0 := h0 (fun _ => state) r0 rfl rfl
    have e1 := h1 (fun _ => state) r1 rfl rfl
    have logs := congrArg (fun r : RunView => r.1.length) (e0.trans e1.symm)
    change 0 = 1 at logs
    exact Nat.noConfusion logs
  · exact ⟨.done (some r0), r0, rfl, rfl, rfl, h0⟩

/-- Even true interpretations of all four named runtime slots do not fix
an unconstrained Runtime. This is a logical interface obstruction, not a
counterexample to the frozen program or to Solana. -/
theorem true_runtime_slots_insufficient (D : LiteralByteProtocol.Decoder)
    (rust : Verifier) (P : Prover) (i : Input) (state : State) :
    True ∧ True ∧ True ∧ True ∧
      ∃ runtime : Runtime, ¬ StoredCarrierBinding D rust P runtime := by
  obtain ⟨runtime, run, _, _, _, h⟩ := same_bytes_insufficient D rust P i state
  exact ⟨True.intro, True.intro, True.intro, True.intro, runtime, h⟩

#print axioms same_bytes_insufficient
#print axioms true_runtime_slots_insufficient
end AspisR1.StoredCarrierBindingObstruction
end
