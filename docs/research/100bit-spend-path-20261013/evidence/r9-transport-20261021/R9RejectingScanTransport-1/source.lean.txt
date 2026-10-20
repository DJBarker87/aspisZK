import R9C3Transport

/-! Acceptance-preserving source coupling needs no unconditional uniform scan
law. An exhausted source scan rejects, so it cannot add accepted failures.
This is the stronger soundness route anticipated by QUERYSCAN. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.R9RejectingScanTransport
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.CausalFirstHitUnionBound AspisV8R19.OracleResampling
open R9TwoTransactionExperiment RawRecordedOracleExtractionMass R1FinalSoundness
open RawCutProverCompiler RawCutTranscriptRun
open BinChecksAdaptiveFailureNoModel BinDecoderCompletionBoundary

/-- R4/R9 source execution fact: a scan exhaustion cannot reach an accepting
stage-2 outcome. Includes source scan/driver correspondence and error propagation. -/
def ScanRejects {C : Type} (source : Program Bytes State (Outcome C)) : Prop :=
  ∀ H : Bytes → State, abort (eval H source) →
    ∀ run, (eval H source).2.resumed = some run → run.2.2 ≠ true

/-- Pointwise accepted-execution refinement on every oracle, including bad
scan tapes. There is no probability law or independence hypothesis here. -/
def AcceptedSourceRefinement {C : Type}
    (source : Program Bytes State (Outcome C)) (model : Experiment) : Prop :=
  ∀ H : Bytes → State, ∀ run, (eval H source).2.resumed = some run →
    run.2.2 = true → run = eval H model

theorem accepted_refinement {C : Type} (source : Program Bytes State (Outcome C))
    (model : Experiment) (hrefine : OrderedSourceRefinement source model)
    (hreject : ScanRejects source) : AcceptedSourceRefinement source model := by
  intro H run hr ha
  by_cases he : abort (eval H source)
  · exact False.elim (hreject H he run hr ha)
  · exact hrefine H he run hr

/-- Shared-oracle failure transport with zero scan charge. -/
theorem transport_no_scan_charge {C : Type}
    (source : Program Bytes State (Outcome C)) (model : Experiment)
    (hrefine : AcceptedSourceRefinement source model) :
    lazyMean source emptyTable deployedMass ≤ lazyMean model emptyTable failureMass := by
  apply OracleProgramLawExt.lazyMean_le_of_eval
  intro H
  apply mean_mono
  intro coins
  apply indicator_mono
  rintro ⟨run, hr, ha, hf⟩
  have he := hrefine H run hr ha
  exact ⟨by simpa only [← he] using ha, by simpa only [← he] using hf⟩

theorem failureProbability_nonneg (N : Nat) :
    0 ≤ QueryScanModelFailure.failureProbability N := by
  unfold QueryScanModelFailure.failureProbability
  positivity

/-- Exact C3 handoff, using the stronger acceptance coupling. The query term
is retained only to match C3's interface, and is not needed by the proof. -/
theorem c3_transport {C : Type}
    (tx1 : Program Bytes State (First C)) (tx2 : C → Program Bytes State Run)
    (D : LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool) (P : Prover)
    (hrefine : OrderedSourceRefinement (R9TwoTransactionExperiment.experiment tx1 tx2)
      (recorded D d P))
    (hreject : ScanRejects (R9TwoTransactionExperiment.experiment tx1 tx2)) :
    DeployedTransport D d P (R9C3Transport.deployedFailure tx1 tx2) := by
  have h := transport_no_scan_charge _ _ (accepted_refinement _ _ hrefine hreject)
  exact h.trans (le_add_of_nonneg_right (failureProbability_nonneg (2^18)))

/-- Evidence-indexed replacement for C3 h_R9_transport via source rejection. -/
theorem c3_transport_obligation {C : Type}
    (tx1 : Program Bytes State (First C)) (tx2 : C → Program Bytes State Run)
    (D : LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool) (P : Prover)
    (s : BoundaryStatements)
    (hrefine : BoundaryEvidence s →
      OrderedSourceRefinement (R9TwoTransactionExperiment.experiment tx1 tx2)
        (recorded D d P))
    (hreject : BoundaryEvidence s →
      ScanRejects (R9TwoTransactionExperiment.experiment tx1 tx2)) :
    BoundaryEvidence s → DeployedTransport D d P (R9C3Transport.deployedFailure tx1 tx2) := by
  intro evidence
  exact c3_transport tx1 tx2 D d P (hrefine evidence) (hreject evidence)

/-- M9 binary consumer from source execution facts alone at the R9 boundary:
ordered same-statement recording and scan rejection, with no uniform-word or
supplied failure-probability premise. Existing M9 inputs are unchanged. -/
theorem source_binary_failure_bound {C : Type}
    (tx1 : Program Bytes State (First C)) (tx2 : C → Program Bytes State Run)
    (D : LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool) (P : Prover) (Q : Nat)
    (hrefine : OrderedSourceRefinement (R9TwoTransactionExperiment.experiment tx1 tx2)
      (recorded D d P))
    (hreject : ScanRejects (R9TwoTransactionExperiment.experiment tx1 tx2))
    (hQ : ∀ H : Bytes → State,
      firstReads emptyTable (eval H (original D d P)).1 ≤ Q + 1161)
    (htag : ∀ H : Bytes → State, (eval H (original D d P)).2.1.1.tag = 2)
    (hchecks : CheckedAcceptance D d P)
    (hknown : LiteralCompletion D d P (Q + 1161))
    (hN : ∀ H : Bytes → State, DecodedFirstReadUnionBound.decoderFirstReads dec
      emptyTable (eval H (recorded D d P)).1 ≤ 33) :
    BinaryClean D d P (Q + 1161) ∧
    R9C3Transport.deployedFailure tx1 tx2 ≤ R1FinalSoundnessNumeric.totalBound Q ∧
    (Q ≤ R1FinalSoundnessNumeric.maxAdversaryQueries →
      R9C3Transport.deployedFailure tx1 tx2 < 1 / (2 : ℚ)^100) :=
  BinM9C3Closure.composed_binary_failure_bound_known_public
    D d P Q (R9C3Transport.deployedFailure tx1 tx2) hQ htag hchecks hknown hN
    (c3_transport tx1 tx2 D d P hrefine hreject)

#print axioms accepted_refinement
#print axioms transport_no_scan_charge
#print axioms failureProbability_nonneg
#print axioms c3_transport
#print axioms c3_transport_obligation
#print axioms source_binary_failure_bound
end AspisR1.R9RejectingScanTransport
end
