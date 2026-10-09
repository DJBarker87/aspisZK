import FSV8S8SelectedOrdinaryTerminal
import FSV8S7DynamicSuccessfulCut
import S8ConcreteCommitmentCuts

/-!
# Terminal-checked execution constructs its commitment cuts

This bridge combines two independently executed facts about one selected run:

* `FSV8S8SelectedOrdinaryTerminal.verifierScript` executes the ordinary
  relation-terminal comparison; and
* the successful semantic prefix constructs the chronological C1/C2 execution
  cuts from that same body and oracle history.

No cut, history, terminal equation, semantic state, or suffix record is a
caller input.  These are verifier-execution cuts, not claims that the verifier
was the first creator of either hash input in the shared adversarial oracle.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 400000
set_option maxRecDepth 2200

namespace AspisV8Completion.FSV8S8TerminalExecutionCuts

open FSOracleExecution FSBoundedTranscript
open FSLiveSemanticPrefix SameBodySemanticWire
open FSV8S4VerifierOnlySuffix
open FSV8S8SelectedOrdinaryTerminal

noncomputable section

abbrev Bytes := List UInt8
abbrev B := FSBoundedTranscript.Block

/-- A successful terminal-checked selected execution constructs its exact
semantic decomposition, chronological same-body root cuts, selected suffix,
and ordinary terminal equation.  The only success premise is the result of
executing the concrete terminal-checked script itself. -/
theorem successful_run_constructs_terminal_execution_cuts
    (binding : Binding) (body : Bytes)
    (tape : FSBoundedTranscript.Tape) (initial : Oracle)
    (accepted : FSV8S8SelectedOrdinaryTerminal.Success body) (digest : B)
    (success :
      (run tape (FSV8S8SelectedOrdinaryTerminal.verifierScript binding body)
        initial).1 = some (.ok accepted, digest)) :
    ∃ postSemantic postSuffix,
      ∃ cuts : S8ConcreteCommitmentCuts.SemanticExecutionCuts true binding body
          tape initial postSemantic accepted.relaxed.semantic,
      ∃ result,
      run tape (semanticScript true binding body) initial =
        (some (.ok accepted.relaxed.semantic), postSemantic) ∧
      SameBodySemanticWire.parse body = some cuts.wire ∧
      run tape (S8SemanticSegments.beforeC1 true binding) initial =
        (some cuts.beforeDigest, cuts.c1Cut) ∧
      run tape (S8SemanticSegments.throughC2 cuts.wire cuts.beforeDigest)
          cuts.c1Cut = (some (.ok cuts.phase), cuts.postC2) ∧
      run tape (S8SemanticSegments.afterC2 body cuts.wire cuts.phase) cuts.postC2 =
        (some (.ok accepted.relaxed.semantic), postSemantic) ∧
      Prefix initial cuts.c1Cut ∧
      Prefix cuts.c1Cut cuts.postC2 ∧
      Prefix cuts.postC2 postSemantic ∧
      run tape
          (selectedSuffixBeforePoints accepted.relaxed.semantic.z
            (FSV8S7DynamicSelectedRoot.operationalCuts cuts.wire) body
            accepted.relaxed.semantic.finalDigest)
          postSemantic =
        (some (.ok accepted.relaxed.record, digest), postSuffix) ∧
      (run tape
          (FSV8S8SelectedOrdinaryTerminal.verifierScript binding body)
          initial).2 = postSuffix ∧
      accepted.relaxed.finalDigest = digest ∧
      FSV8S8SelectedOrdinaryTerminal.operands accepted.relaxed = some result ∧
      result.expected = result.carried := by
  have terminal :=
    FSV8S8SelectedOrdinaryTerminal.successful_run_constructs_terminal_equation
      binding body tape initial accepted digest success
  have sourceSuccess :
      (run tape
        (FSV8S7DynamicSelectedRoot.verifierScript true binding body) initial).1 =
          some (.ok accepted.relaxed, digest) := by
    simpa [FSV8S7DynamicSelectedRoot.selectedVerifierScript] using terminal.1
  obtain ⟨wire, postSemantic, postSuffix, parsed, semanticRun, suffixRun,
      sourceFinalOracle, finalDigest⟩ :=
    FSV8S7DynamicSuccessfulCut.successful_verifier_constructs_post_semantic_cut
      true binding body tape initial accepted.relaxed digest sourceSuccess
  obtain ⟨cuts⟩ :=
    S8ConcreteCommitmentCuts.successful_semantic_constructs_execution_cuts
      true binding body tape initial postSemantic accepted.relaxed.semantic semanticRun
  have wireEq : cuts.wire = wire := by
    exact Option.some.inj (cuts.parsed.symm.trans parsed)
  subst wire
  obtain ⟨prefixInitial, prefixC1, prefixC2⟩ :=
    S8ConcreteCommitmentCuts.execution_cuts_are_prefixes cuts
  obtain ⟨result, operandsEq, terminalEq⟩ := terminal.2
  have checkedFinalOracle :
      (run tape
        (FSV8S8SelectedOrdinaryTerminal.verifierScript binding body) initial).2 =
          postSuffix := by
    calc
      _ = (run tape
          (FSV8S7DynamicSelectedRoot.selectedVerifierScript binding body)
          initial).2 :=
        FSV8S8SelectedOrdinaryTerminal.verifierScript_final_oracle
          binding body tape initial
      _ = postSuffix := sourceFinalOracle
  exact ⟨postSemantic, postSuffix, cuts, result, semanticRun, cuts.parsed,
    cuts.beforeRun, cuts.throughRun, cuts.afterRun, prefixInitial, prefixC1,
    prefixC2, suffixRun, checkedFinalOracle, finalDigest, operandsEq, terminalEq⟩

#print axioms successful_run_constructs_terminal_execution_cuts

end
end AspisV8Completion.FSV8S8TerminalExecutionCuts
