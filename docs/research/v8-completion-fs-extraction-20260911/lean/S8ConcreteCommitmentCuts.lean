import S8SemanticSegments

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 400000
namespace AspisV8Completion.S8ConcreteCommitmentCuts
open FSOracleExecution FSBoundedTranscript FSTranscriptScript
open FSLiveSemanticPrefix S8SemanticSegments FSNonzeroQM31 S8RunLevelBind
open FSV7OODSampler
noncomputable section
abbrev Bytes := List UInt8

def capture (positive : Bool) (binding : Binding) (body : Bytes)
    (tape : Tape) (initial : Oracle) : Option RootCuts := do
  let wire ← SameBodySemanticWire.parse body
  let digest ← (run tape (beforeC1 positive binding) initial).1
  let before : Transcript := ⟨digest, (run tape (beforeC1 positive binding) initial).2⟩
  let c1 := absorb tape before 3 (List.ofFn (wire.roots 0))
  let l := challenge tape c1
  let lambda ← l.1
  let c := challenge tape l.2
  let chi ← c.1
  let final := absorb tape c.2 9 (List.ofFn (wire.roots 1))
  pure ⟨wire.roots 0, wire.roots 1, before.oracle, c.2.oracle, final, lambda, chi⟩

/-- The chronological C1/C2 cut computation after the statement digest is
already produced.  This is useful for connecting the script interpreter to
the direct transcript functions without rerunning any prior phase. -/
def captureAfterBefore (wire : SameBodySemanticWire.Wire) (digest : Block)
    (tape : Tape) (beforeOracle : Oracle) : Option RootCuts := do
  let before : Transcript := ⟨digest, beforeOracle⟩
  let c1 := absorb tape before 3 (List.ofFn (wire.roots 0))
  let l := challenge tape c1
  let lambda ← l.1
  let c := challenge tape l.2
  let chi ← c.1
  let final := absorb tape c.2 9 (List.ofFn (wire.roots 1))
  pure ⟨wire.roots 0, wire.roots 1, beforeOracle, c.2.oracle, final, lambda, chi⟩

/-! `SemanticExecutionCuts` records only facts produced by one literal run.
Unlike `RootCuts`, it does not duplicate raw challenge limbs by replaying the
transcript functions.  That stronger raw-limb refinement remains a separate
bridge. -/
structure SemanticExecutionCuts (positive : Bool) (binding : Binding)
    (body : Bytes) (tape : Tape) (initial final : Oracle) (state : Success) where
  wire : SameBodySemanticWire.Wire
  beforeDigest : Block
  c1Cut : Oracle
  phase : Phase2
  postC2 : Oracle
  parsed : SameBodySemanticWire.parse body = some wire
  beforeRun : run tape (beforeC1 positive binding) initial =
    (some beforeDigest, c1Cut)
  throughRun : run tape (throughC2 wire beforeDigest) c1Cut =
    (some (.ok phase), postC2)
  afterRun : run tape (afterC2 body wire phase) postC2 =
    (some (.ok state), final)

/-- A successful literal semantic execution constructs its same-body parsed
wire and the actual interpreter states immediately before C1 and after C2.
These are verifier execution cuts, not first-creator/freshness cuts. -/
theorem successful_semantic_constructs_execution_cuts
    (positive : Bool) (binding : Binding) (body : Bytes)
    (tape : Tape) (initial final : Oracle) (state : Success)
    (success : run tape (semanticScript positive binding body) initial =
      (some (.ok state), final)) :
    Nonempty (SemanticExecutionCuts positive binding body tape initial final state) := by
  have factorised := actual_semantic_run_factorises positive binding body tape initial
  rw [success] at factorised
  have firstSuccess :
      (run tape (semanticScript positive binding body) initial).1 = some (.ok state) := by
    rw [success]
  obtain ⟨wire, parsed, _⟩ :=
    successful_run_has_same_body_wire positive binding body tape initial state firstSuccess
  simp only [factored, parsed] at factorised
  obtain ⟨beforeDigest, beforeOracle, beforeRun, remainderRun⟩ :=
    successful_bind_split tape (beforeC1 positive binding)
      (fun digest => bind (m := 1663) (throughC2 wire digest) fun second =>
        match second with
        | .error e => .done (.error e)
        | .ok phase => afterC2 body wire phase)
      initial final (.ok state) factorised.symm
  obtain ⟨second, postC2, phaseRun, tailRun⟩ :=
    successful_bind_split tape (throughC2 wire beforeDigest)
      (fun second => match second with
        | .error e => .done (.error e)
        | .ok phase => afterC2 body wire phase)
      beforeOracle final (.ok state) remainderRun
  cases second with
  | error e => cases tailRun
  | ok phase =>
    exact ⟨⟨wire, beforeDigest, beforeOracle, phase, postC2, parsed,
      beforeRun, phaseRun, tailRun⟩⟩

/-- Every constructed execution cut is chronological in the shared oracle. -/
theorem execution_cuts_are_prefixes
    {positive : Bool} {binding : Binding} {body : Bytes} {tape : Tape}
    {initial final : Oracle} {state : Success}
    (cuts : SemanticExecutionCuts positive binding body tape initial final state) :
    Prefix initial cuts.c1Cut ∧ Prefix cuts.c1Cut cuts.postC2 ∧
      Prefix cuts.postC2 final := by
  have beforePrefix := run_extends tape (beforeC1 positive binding) initial
  have throughPrefix := run_extends tape
    (throughC2 cuts.wire cuts.beforeDigest) cuts.c1Cut
  have afterPrefix := run_extends tape
    (afterC2 body cuts.wire cuts.phase) cuts.postC2
  rw [cuts.beforeRun] at beforePrefix
  rw [cuts.throughRun] at throughPrefix
  rw [cuts.afterRun] at afterPrefix
  exact ⟨beforePrefix, throughPrefix, afterPrefix⟩

#print axioms successful_semantic_constructs_execution_cuts
#print axioms execution_cuts_are_prefixes
end
end AspisV8Completion.S8ConcreteCommitmentCuts
