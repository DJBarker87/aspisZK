import RawExtractorCostComposedV2
import DecoderInstanceBoundary
import BinCombinedMerkleCollision
import QueryScanModelFailure
import R1FinalSoundnessNumeric

/-! C3 conditional composition on the frozen b2727acd3 verifier.
This file constructs neither a deployed decoder nor a source simulation.
Every source law below is an explicit hypothesis. In particular the binary
completion/word transport cannot be obtained by halving historical M9. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.R1FinalSoundness
open FS FS2 R0C.V3
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.CausalFirstHitUnionBound
open RawCutProverCompiler RawCutTranscriptRun
open RawRecordedOracleExtractionMass RawExtractorCostComposedV2
open DecoderInstanceBoundary

open LiteralAcceptanceTerminal

/-- External statements about the pinned artifacts. These proposition slots
are intentional: compiler correctness and runtime semantics have no internal
Lean definition here. Their interpretation is fixed in C3-SKELETON-20261020.md;
a caller must supply both the statements and proofs/acceptance below. -/
structure BoundaryStatements where
  /-- P1: SHA-256 ROM/collision/target-preimage properties; premise reacceptance §P1. -/
  P1 : Prop
  /-- P2: ownership, permissions, locks, rollback, persistence; reacceptance §P2 and R15 write audit. -/
  P2 : Prop
  /-- P2′: same complete proof/public input bytes when checkpoint digests match; R15 read audit, Exact remaining account-boundary premise. -/
  P2_prime : Prop
  /-- P3: concatenated SHA, stored-bump PDA and System semantics; reacceptance §P3/J1.R16. -/
  P3 : Prop
  /-- P4: observed owner/signer/writable/executable equal runtime metadata; R16ReadonlyMetadataBoundary:23. -/
  P4 : Prop
  /-- P5/F6: canonical initializer provenance for stored bumps and hints; reacceptance §P5. -/
  P5 : Prop
  /-- P6: pinned Charon/Aeneas/Lean/mathlib correctness; reacceptance §P6, coherent C2 replay owed. -/
  P6 : Prop
  /-- P7: pinned source-to-SBF toolchain correctness; reacceptance §P7, freeze b2727acd3. -/
  P7 : Prop
  /-- R10: one consistent, complete tx1/tx2 byte log; LOG-TX2-20261020, complete coverage still owed. -/
  R10 : Prop
  /-- R22: wrapping-source accepts implies checked-source accepts, both cones; OVERFLOW-FREEDOM-S2-20261020. -/
  R22 : Prop
  /-- R4/R18: scalar/circle carriers and full prefix transport; SAMPLER-ROWS-25-32-20261020. -/
  R4_transport : Prop
  /-- R17: source folds/geometry and stored-domain tables; FOLD-GEOMETRY-20261020, S7 join. -/
  R17 : Prop
  /-- R20/R9: Pool ASQ8 reconstruction/CPI handoff for both variants; TRANSFER-BINDINGS-20261020 and adapter audits. -/
  R20 : Prop
  /-- R21/C1: source/feature/extraction/ELF identity at freeze; LEAD-FREEZE-20261020. -/
  R21 : Prop
  /-- S1 candidate 1: reused gamma powers/Prepared/tx1 body refinement; gap map §2c, re-pin owner Codex. -/
  S1 : Prop
  /-- S2 candidate 2: observer off and adapter caller; REPIN-s2-20261020 plus adapter read audit (verifier half proved). -/
  S2 : Prop
  /-- S3 candidate 3: all inactive group/table bits and source classification; gap map §2c. -/
  S3 : Prop
  /-- S4 candidates 4/10: actual four_dots loop/batch and fixed prefix correspondence; FastDotFoldedBatches is only algebra. -/
  S4 : Prop
  /-- S5 candidate 5: private canonical pairing/dot kernels and actual callers; gap map §2c. -/
  S5 : Prop
  /-- S6 candidate 6: first/first_decoded and same-byte caller binding; REPIN-s6-20261020 plus read audit (verifier half proved). -/
  S6 : Prop
  /-- S7 candidate 7: production query_values/accumulate_batched_with_node; REPIN-s7-20261020, next-freeze blocker. -/
  S7 : Prop
  /-- S8 candidate 12: accumulator/residue finish and compact check_values; REPIN-s8-20261020, next-freeze blocker. -/
  S8 : Prop
  /-- S9 candidate 14: factored S2 Libra machine arithmetic and loops; gap map §2c. -/
  S9 : Prop
  /-- S10: complete declaration inventory at the frozen ref, reconciled to production owners; gap map §2c. -/
  S10 : Prop
  /-- M10: uniformly bounded input-size parameters and one overhead constant/degree
  for the implementation family; extractor-cost-composed-20261019, remaining
  implementation hypotheses. Needed for the polynomial-family interpretation. -/
  M10_uniform : Prop

/-- Named acceptance/evidence arguments, never axioms. P1–P7/P2′ are accepted
premises only if the lead explicitly reaccepts them for the freeze; the draft
reacceptance file itself records no such acceptance. S2/S6 retain their
already-proved halves and audited caller halves as explicit release evidence. -/
structure BoundaryEvidence (s : BoundaryStatements) : Prop where
  /-- P1: SHA-256 ROM/collision/target-preimage properties; premise reacceptance §P1. -/
  h_P1 : s.P1
  /-- P2: ownership, permissions, locks, rollback, persistence; reacceptance §P2 and R15 write audit. -/
  h_P2 : s.P2
  /-- P2′: same complete proof/public input bytes when checkpoint digests match; R15 read audit, Exact remaining account-boundary premise. -/
  h_P2_prime : s.P2_prime
  /-- P3: concatenated SHA, stored-bump PDA and System semantics; reacceptance §P3/J1.R16. -/
  h_P3 : s.P3
  /-- P4: observed owner/signer/writable/executable equal runtime metadata; R16ReadonlyMetadataBoundary:23. -/
  h_P4 : s.P4
  /-- P5/F6: canonical initializer provenance for stored bumps and hints; reacceptance §P5. -/
  h_P5 : s.P5
  /-- P6: pinned Charon/Aeneas/Lean/mathlib correctness; reacceptance §P6, coherent C2 replay owed. -/
  h_P6 : s.P6
  /-- P7: pinned source-to-SBF toolchain correctness; reacceptance §P7, freeze b2727acd3. -/
  h_P7 : s.P7
  /-- R10: one consistent, complete tx1/tx2 byte log; LOG-TX2-20261020, complete coverage still owed. -/
  h_R10 : s.R10
  /-- R22: wrapping-source accepts implies checked-source accepts, both cones; OVERFLOW-FREEDOM-S2-20261020. -/
  h_R22 : s.R22
  /-- R4/R18: scalar/circle carriers and full prefix transport; SAMPLER-ROWS-25-32-20261020. -/
  h_R4_transport : s.R4_transport
  /-- R17: source folds/geometry and stored-domain tables; FOLD-GEOMETRY-20261020, S7 join. -/
  h_R17 : s.R17
  /-- R20/R9: Pool ASQ8 reconstruction/CPI handoff for both variants; TRANSFER-BINDINGS-20261020 and adapter audits. -/
  h_R20 : s.R20
  /-- R21/C1: source/feature/extraction/ELF identity at freeze; LEAD-FREEZE-20261020. -/
  h_R21 : s.R21
  /-- S1 candidate 1: reused gamma powers/Prepared/tx1 body refinement; gap map §2c, re-pin owner Codex. -/
  h_S1 : s.S1
  /-- S2 candidate 2: observer off and adapter caller; REPIN-s2-20261020 plus adapter read audit (verifier half proved). -/
  h_S2 : s.S2
  /-- S3 candidate 3: all inactive group/table bits and source classification; gap map §2c. -/
  h_S3 : s.S3
  /-- S4 candidates 4/10: actual four_dots loop/batch and fixed prefix correspondence; FastDotFoldedBatches is only algebra. -/
  h_S4 : s.S4
  /-- S5 candidate 5: private canonical pairing/dot kernels and actual callers; gap map §2c. -/
  h_S5 : s.S5
  /-- S6 candidate 6: first/first_decoded and same-byte caller binding; REPIN-s6-20261020 plus read audit (verifier half proved). -/
  h_S6 : s.S6
  /-- S7 candidate 7: production query_values/accumulate_batched_with_node; REPIN-s7-20261020, next-freeze blocker. -/
  h_S7 : s.S7
  /-- S8 candidate 12: accumulator/residue finish and compact check_values; REPIN-s8-20261020, next-freeze blocker. -/
  h_S8 : s.S8
  /-- S9 candidate 14: factored S2 Libra machine arithmetic and loops; gap map §2c. -/
  h_S9 : s.S9
  /-- S10: complete declaration inventory at the frozen ref, reconciled to production owners; gap map §2c. -/
  h_S10 : s.S10
  /-- M10 uniform-family obligation; not inferred from a finite-instance ledger.
  Owner Codex; extractor-cost-composed-20261019 and RawExtractorCostComposedV2:119. -/
  h_M10_uniform : s.M10_uniform

/-- Data selected from an authenticated execution. No correctness is smuggled
into this carrier: the following row laws must prove each field's use. -/
structure SourceInputs where
  decoded : R0P.Public SemanticPublicWire.M31
  data : MatchingSupport.Data E
  m31 : LiteralTranscript.Message
  queryBytes : List Nat
  state31 : State
  m32 : LiteralTranscript.Message
  rho : E
  state32 : State

abbrev original (D : LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool) (P : Prover) := experiment P (verifier D d)
abbrev recorded (D : LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool) (P : Prover) :=
  AcceptedAdaptiveFiatShamir.experiment
    (compiled D d (RawCutWordsFromView.buildWords D) P) (verifier D d)
abbrev dec := RawAdaptiveLiteralDecoder.decode RawFullPublicSelection.select LiteralTableWordChoice.choose
abbrev binaryCollision (Q : Nat) (run : RunView) : Prop :=
  BinCombinedMerkleCollision.Coll SelectedTranscriptParams.params.iv Q run

/-- R16 instance/source-to-compiled-rows obligations, not a free terminal
Boolean. DECODER-INSTANCE-20261020 and HCHECKS-20261020 name the evidence still
needed from R14, frozen R15, R9, R-wire and S1–S10. -/
def InstanceFields (D : LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool) (P : Prover)
    (H : Bytes → State) (i : SourceInputs) : Prop :=
  SemanticPublicWire.parsePublic (compiledPublic D d P H).pubBytes = some i.decoded ∧
  (compiledRows D d P H)[31]? = some (i.m31,
    (TranscriptView.Value.queries (.ok i.queryBytes), i.state31)) ∧
  (compiledRows D d P H)[32]? = some (i.m32,
    (TranscriptView.Value.ordinary i.rho, i.state32)) ∧
  LiteralTranscript.valid 31 i.m31 ∧ LiteralTranscript.valid 32 i.m32

/-- R-wire binary completion: exactly LazyInj.decodes for the five-reader
binary collision event. BIN-COMMITMENT-MODEL §6 explicitly leaves this
consumer bridge open; WIRE-TX1/TX2 and R12/R13 must discharge it. -/
def BinaryCompletion (D : LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool) (P : Prover) (Q : Nat) : Prop :=
  ∀ H : Bytes → State, ¬ binaryCollision Q (eval H (recorded D d P)) →
    FS2.accepts (eval H (recorded D d P)) →
    ∀ n a, n < (LiteralByteProtocol.protocol D).r →
      firstCell ((LiteralByteProtocol.protocol D).chain H
        (eval H (recorded D d P)).2.1.1 (eval H (recorded D d P)).2.1.2 n) = some a →
      ∃ own pend g, dec a (tableBefore emptyTable (eval H (recorded D d P)).1 a) =
          some (own, pend, g) ∧
        bfollow g (traceFrom (eval H (recorded D d P)).1 a) own pend
          (tableBefore emptyTable (eval H (recorded D d P)).1 a) =
          some ((LiteralByteProtocol.protocol D).transcript H
              (eval H (recorded D d P)).2.1.1 (eval H (recorded D d P)).2.1.2 n,
            (LiteralByteProtocol.protocol D).msg (eval H (recorded D d P)).2.1.2 n,
            (LiteralByteProtocol.protocol D).chal H
              (eval H (recorded D d P)).2.1.1 (eval H (recorded D d P)).2.1.2 n)

/-- Binary R12/M7/M8 word alignment on the actual recorded extractor, including
failure-preserving decoding. R12-WORDS-20261020 and BIN-COMMITMENT-MODEL §6:
binary stability alone does not instantiate the old clean-model consumer. -/
def BinaryClean (D : LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool) (P : Prover) (Q : Nat) : Prop :=
  CleanAcceptedModel D (recorded D d P) (fun run => binaryCollision Q run ∨
    hitsChain3 dec RawAdaptiveClassifierHitDensity.classifier emptyTable run.1)

/-- The deployed target's probability is an external carrier until R9/R20,
R10 and R16 give the source execution law. It must charge query-scan aborts
once. This is a probability transport obligation, not the target bound. -/
def DeployedTransport (D : LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool) (P : Prover) (deployedFailure : ℚ) : Prop :=
  deployedFailure ≤ lazyMean (recorded D d P) emptyTable failureMass +
    QueryScanModelFailure.failureProbability (2^18)

/-- (T), conditional on the explicitly named source laws and external
premises. Owners/evidence for every argument are in C3-SKELETON-20261020.
N=33 is a decoded-start assumption, never inferred from a hash-query cap.
M9's historical bound is retained as a separate conclusion via M10; the
binary bound uses a new injection with the proved five-reader collision mass.
The deployed probability carrier must denote acceptance without a relation
witness/extractor success, as specified by DeployedTransport.

Hypothesis documentation (all evidence paths relative to the research root):
* `h_R16_instance` (R16, R6/R8/R9): authenticated source to the exact public
  parse and rows; design/DECODER-INSTANCE-20261020.md and its instance obstruction.
* `h_R4_row31` (R4 row 31): source QueryScan success gives 22 distinct in-range
  indices; design/QUERYSCAN-20261020.md (concrete driver/coupling still owed).
* `h_R13` (R13): accepted logged matching data; design/R13-CLOSE-20261020.md
  (whole dedup/18-level simulation/zero-scan/read coverage/batch A remain).
* `h_R14_backend` (R14): actual pairing and accumulator endpoints;
  design/R14-FINISH-20261020.md (S4/S5/S8/S9 and finalisation still owed).
* `h_R15_writer` (R15): authenticated first-match state for the same transcript;
  design/TX1-FINISH-20261020.md and both R15 adapter audits (writer remains open).
* `h_R3_semantic` (R3/R2): the literal semantic endpoint;
  design/HCHECKS-20261020.md and the finish-model boundary obligations.
* `h_R18` (R18): universal tag 2 under the deployed public mapping;
  design/SAMPLER-ROWS-25-32-20261020.md and DECODER-INSTANCE.
* `h_R19` (R19): all-input first reads, adversary plus 595+566;
  design/QV-STAGE1-20261020.md and QV-STAGE2 (source coverage remains).
* `h_Rwire` (R-wire): binary completion outside the five-reader event;
  design/BIN-COMMITMENT-MODEL-20261019.md §6 and WIRE-TX1/TX2.
* `h_R12_binary_words` (R12/M7/M8): binary clean-word/extractor alignment;
  design/R12-WORDS-20261020.md and BIN-COMMITMENT-MODEL §6.
* `h_R9_transport` (R9/R20/R10/R16/R4): deployed failure mass transport,
  same statement and query-scan coupling; design/TRANSFER-BINDINGS-20261020.md,
  both R15 audits and QUERYSCAN. This is not a proved deployment law.
* `hN` is M9's adversary decoded-start restriction, not a source theorem.
* `e.value` and `h_M10_ledger` are M10 output and cost refinements;
  lean/RawExtractorCostComposedV2.lean:42,85,124; uniformity additionally
  requires `evidence.h_M10_uniform`. No asymptotic claim follows merely
  from choosing large per-instance overhead constants. -/
theorem final_soundness
    (D : LiteralByteProtocol.Decoder)
    (d : ErasedPrefix → ErasedMessage → Bool) (P : Prover)
    (Q : Nat) (deployedFailure : ℚ)
    (s : BoundaryStatements) (evidence : BoundaryEvidence s)
    (source : (Bytes → State) → SourceInputs)
    /- R16: construct the authenticated decoder/decision map, public bytes and
       exact row-31/32 placements. DECODER-INSTANCE, owner Codex/lead. -/
    (h_R16_instance : BoundaryEvidence s → ∀ H,
      FS2.accepts (eval H (original D d P)) → InstanceFields D d P H (source H))
    /- R4 row31: concrete QueryScan/library/ROM coupling; QUERYSCAN, owner Codex. -/
    (h_R4_row31 : ∀ H, FS2.accepts (eval H (original D d P)) →
      (source H).queryBytes.Nodup ∧ (source H).queryBytes.length = 22 ∧
        ∀ x ∈ (source H).queryBytes, x < 262144)
    /- R13: accepted binary reads give literal matching data; R13-CLOSE,
       batch A on S7, owner Codex. -/
    (h_R13 : ∀ H, FS2.accepts (eval H (original D d P)) →
      LiteralMatchingData.read (compiledRows D d P H) = some (source H).data)
    /- R14 backend: pairing and finalized accumulator; R14-FINISH,
       S4/S5/S8/S9 boundaries, owner Codex. -/
    (h_R14_backend : ∀ H, FS2.accepts (eval H (original D d P)) →
      LiteralPairingChecks.checks (compiledRows D d P H) ∧
      ∀ q : Fin 22 → Fin 262144,
        LiteralQueryRead.decode (source H).queryBytes = some q →
        HchecksAccumulator.ClosedSum LiteralOpeningView.eK (source H).data q
          (SelectedChallengeMap.rhoOf (source H).rho))
    /- R15 writer: authenticated first-match state; TX1-FINISH and read/write
       audits, unconditional frozen-writer preservation still owed, owner Codex. -/
    (h_R15_writer : ∀ H, FS2.accepts (eval H (original D d P)) →
      ∀ q : Fin 22 → Fin 262144,
        LiteralQueryRead.decode (source H).queryBytes = some q →
        ∀ j, MatchingSupport.match0 (source H).data (q j))
    /- R3/R2: actual semantic endpoint with arithmetic/allocation/circle
       boundaries; HCHECKS field table, owner Codex. -/
    (h_R3_semantic : ∀ H, FS2.accepts (eval H (original D d P)) →
      HchecksReaderComposition.SemanticEndpoint (source H).decoded
        (compiledRows D d P H) (source H).data)
    /- R18: deployed tag/public mapping; SAMPLER-ROWS and DECODER-INSTANCE. -/
    (h_R18 : BoundaryEvidence s → ∀ H,
      (eval H (original D d P)).2.1.1.tag = 2)
    /- R19 with R10: all prefixes, designated-core scope; QV-STAGE1/2 and
       complete log/stop/backend correspondence; owner Codex. -/
    (h_R19 : BoundaryEvidence s → ∀ H,
      firstReads emptyTable (eval H (original D d P)).1 ≤
        Q + (QvStage1.stage1Budget 10 + QvStage2.stage2Budget 12))
    /- R-wire: binary causal decoder completion, distinct from collision mass;
       BIN model §6, WIRE-TX1/TX2, owner Codex/privacy. -/
    (h_Rwire : BoundaryEvidence s → BinaryCompletion D d P (Q + 1161))
    /- R12/M7/M8: binary words align to this extractor on clean runs;
       R12-WORDS and BIN model §6, owner Codex. -/
    (h_R12_binary_words : BoundaryEvidence s →
      (∀ H, FS2.accepts (eval H (original D d P)) →
        Checks (compiledPublic D d P H) (compiledRows D d P H)) →
      BinaryClean D d P (Q + 1161))
    /- R9/R20: same statement, caller reachability and probability law,
       including a single query-scan abort charge; owner Codex/lead-worker. -/
    (h_R9_transport : BoundaryEvidence s → DeployedTransport D d P deployedFailure)
    /- Adversary experiment restriction, M9 hN: at most 33 recognized starts. -/
    (hN : ∀ H : Bytes → State, DecodedFirstReadUnionBound.decoderFirstReads dec
      emptyTable (eval H (recorded D d P)).1 ≤ 33)
    (e : CostedExtractor) (p : Parameters)
    /- M10: bounded arithmetic jobs/overhead, actual log reads and bit work;
       RawExtractorCostComposedV2:85, owner Codex. e.value is output refinement.
       A family claim additionally needs uniform parameters as documented. -/
    (h_M10_ledger : LedgerRefinement e p) :
    (∀ H : Bytes → State, (eval H (recorded D d P)).2.2 = true →
      AspisV8R19.OracleResampling.mean (fun coins : Coins =>
        ((e.eval (eval H (recorded D d P)) coins).2.total : ℚ)) ≤ (p.attemptBudget : ℚ)) ∧
    (∀ run coins w, (e.eval run coins).1 = some w → LiteralProtocol.relation run.2.1.1 w) ∧
    (1 / (2 : ℚ)^126 + 1 / (2 : ℚ)^454 ≤ 1 / (2 : ℚ)^120) ∧
    (lazyMean (recorded D d P) emptyTable failureMass ≤
      RawAdaptiveDecoderInjection.kappa (Q + 1161) + 33 * PerAttemptEnvelope.B + 1 / (2 : ℚ)^126) ∧
    (deployedFailure ≤ R1FinalSoundnessNumeric.totalBound Q) ∧
    (Q ≤ R1FinalSoundnessNumeric.maxAdversaryQueries → deployedFailure < 1 / (2 : ℚ)^100) := by
  have hchecks : ∀ H, FS2.accepts (eval H (original D d P)) →
      Checks (compiledPublic D d P H) (compiledRows D d P H) := by
    intro H ha
    obtain ⟨hpub, h31, h32, hv31, hv32⟩ := h_R16_instance evidence H ha
    obtain ⟨hpair, haccum⟩ := h_R14_backend H ha
    exact Classical.choice (hchecks_deployed_partial D d P H
      (source H).decoded (source H).data hpub (h_R13 H ha) hpair
      (source H).m31 (source H).queryBytes (source H).state31
      (source H).m32 (source H).rho (source H).state32
      h31 h32 hv31 hv32 (h_R4_row31 H ha) (h_R15_writer H ha) haccum (h_R3_semantic H ha))
  have hQ : ∀ H, firstReads emptyTable (eval H (original D d P)).1 ≤ Q + 1161 := by
    simpa only [R1FinalSoundnessNumeric.verifier_reads] using h_R19 evidence
  have cost := recorded_extractor_cost_and_failure D d P (Q + 1161) 33
    hQ (h_R18 evidence) hchecks hN e p h_M10_ledger
  have hqc := RawCutCompilerLaw.query_bound_preserved D d
    (RawCutWordsFromView.buildWords D) P (Q + 1161) hQ
  let inj : AcceptedAdaptiveFiatShamir.LazyInj (LiteralByteProtocol.protocol D) dec
      (compiled D d (RawCutWordsFromView.buildWords D) P) (verifier D d)
      BinCombinedMerkleCollision.kappa (Q + 1161) :=
    { Coll := binaryCollision (Q + 1161)
      mass := BinCombinedMerkleCollision.mass SelectedTranscriptParams.params.iv
        (Q + 1161) (recorded D d P) hqc
      decodes := h_Rwire evidence }
  have hb := RawRecordedActualAdaptiveFailureBound.actual_recorded_failure_le_collision_add_start_density_add_abort
    D RawFullPublicSelection.select LiteralTableWordChoice.choose
    (compiled D d (RawCutWordsFromView.buildWords D) P) (verifier D d)
    BinCombinedMerkleCollision.kappa (Q + 1161) 33 inj
    (h_R12_binary_words evidence hchecks) hN
  have hd : deployedFailure ≤ R1FinalSoundnessNumeric.totalBound Q := by
    calc
      deployedFailure ≤ lazyMean (recorded D d P) emptyTable failureMass +
          QueryScanModelFailure.failureProbability (2^18) := h_R9_transport evidence
      _ ≤ (BinCombinedMerkleCollision.kappa (Q + 1161) +
          (33 : ℚ) * PerAttemptEnvelope.B + 1 / (2 : ℚ)^126) + 1 / (2 : ℚ)^454 :=
        add_le_add hb QueryScanModelFailure.exhaustion_bound
      _ = R1FinalSoundnessNumeric.totalBound Q := by
        rfl
  exact ⟨cost.1, cost.2.1, R1FinalSoundnessNumeric.extractor_abort_allowance, cost.2.2.2, hd,
    fun h => hd.trans_lt ((R1FinalSoundnessNumeric.numeric_iff Q).2 h)⟩

#print axioms final_soundness

end AspisR1.R1FinalSoundness
end
