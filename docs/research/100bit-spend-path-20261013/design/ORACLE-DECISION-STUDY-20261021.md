# Oracle decision feasibility study, 2026-10-21

Scope: branch `codex/cx-oracle-dec-20261021`, base `7dac4fa12`.
This is a feasibility study, not a replacement soundness endpoint. No existing
Lean module, endpoint, S-cone candidate, or M10 instrumentation file is changed.
The study reads the complete C3 addenda, including the later R-wire and d₀
obstructions; the requested R19 endpoint remains the comparison baseline.

## Recommendation

Proceed with a staged oracle-decision port, subject to two explicit acceptance
criteria: preserve the query-normalised decoder-start coefficient, and prove a
joint sampler/Merkle budget rather than infer it from `561 ≤ 1161`.
The oracle-program carrier is mathematically viable. It does not by itself
construct the frozen verifier, discharge the semantic/source joins, or repair
arbitrary metadata on all typed inputs.

## 1. Definitions and exact pure embedding

`OracleDecisionFeasibilityCore` defines `Decision := ErasedPrefix →
ErasedMessage → Program Bytes State Bool`, `onBytes`, `lift`, the 33-row
`verifierFrom`/`verifier`, `original`, and a self-recording wrapper `recorded`.
The terminal case executes `dO`; it does not inspect the prover's hidden log.

Checked: `lift_from`, `lift_verifier`, `lift_experiment`, `lift_view`, and
`lift_special_case`. Pure lifting is exact **program equality**, not merely an
acceptance equivalence. Thus evaluation, all log projections, public output,
acceptance, any event, and any probability functional on the same program
transport by rewriting. This means old theorems are special cases; it does not
mean every old theorem is already proved for arbitrary effectful decisions.

`OracleDecisionFeasibilityCompiler` additionally ports enrichment congruence,
`eval_compiled`, `compiled_experiment_eval`, `public_and_acceptance`,
`firstReads_eq`, and `commitment_cut_eq`. Its `lift_compiled` and
`lift_compiled_experiment` identify the annotated accepted-experiment shape
used by the endpoint exactly with the existing compiler on pure lifting.
The core self-recording wrapper and the endpoint's compiled experiment are
intentionally distinct definitions.

The existing `OracleVerifier.lean` already contains a generic terminal-program
verifier and done-specialisation, as well as chain/terminal read inclusion.
Our distinct-prefix modules instantiate the same recurrence without editing
that module; a production port should reuse its API.

## 2. Inventory and purity-sensitive claims

Reproducible audit: `evidence/oracle-dec-20261021/inventory.py`, with
`inventory.json` (exact matched text) and `inventory.md` (declaration/line index
and per-declaration assessment). Roots include R19, R-wire, R9, canonical and
d₀ helpers; local transitive imports comprise 458 modules, including historical
helper imports, with 73 textual pure-signature modules. The 459 matched lines
span 261 declarations. This is a textual audit, not a kernel dependency claim;
incidental uses of list length or first reads are marked unchanged.

| Existing theorem/family | Assessment for oracle decisions |
|---|---|
| `RawCutTranscriptRun.decision_enrich`, `verifierFrom_eq`, `verifier_eq` | A: unchanged reasoning. Erasure equality makes the **entire decision program** equal, even with adaptive queries. Checked in the compiler prototype. |
| `RawCutProverCompiler.eval_compiled`, `compiled_experiment_eval`, `public_and_acceptance`, `firstReads_eq`, `commitment_cut_eq` | A: unchanged. Internal execution records the whole verifier, including terminal reads; external execution repeats that whole suffix under fixed H. Checked prototype. |
| `OracleProgramRecording.eval_record`, `firstReads_append_reused`, `firstReads_repeat_suffix`; `RawCutCompilerDecoderStartLaw.decoderStarts_eq`, `decoderStart_bound_preserved`; `RawCutCompilerLaw` probability/query transfer | A: already generic in program/log/decoder or a direct compiler replay port. No pure-decision assumption in the repeat-suffix fact. |
| `OracleProgramReplay.eval_eq_of_agrees`, `eval_oracleOf` | A: already generic programs. |
| `OracleProgramReplay.transcript_eq_of_agrees`; `RawCutWordsFromView.recorded_transcript_eq`, `frameFromView_eq`, `frame_read`; `BinCompiledRunWordStability` | A: replace the old pure verifier-read helper with chain inclusion in the new full trace; transcript construction still uses only sampler reads. |
| `RawCutLiteral*Order`, `*Adjacent`, `*InitialAdvanceRead`, `*NextFrame` and corresponding `RWireRawCut*` copies | A: chain reads and within-chain order remain present; appended decision reads do not move first indices of addresses already present. Pure helper applications need program-valued counterparts. |
| `FS2.verifierFrom_eval`, `FS2.verifier_eval` | Existing **sampler-only** formula fails if directly asserted for dO. Generalises with terminal log appended and terminal evaluated output; checked in `OracleDecisionFeasibilityBudget.from_eval`/`verifier_eval`. |
| `LiteralLegacyVerifierTrace.trace_eq_map`, `restricted_trace_eq`, `verifier_trace_canonical` | C: full-trace equality or all-label canonicality breaks for arbitrary terminal byte queries. Keep the sampler prefix for legacy selection proofs, then append the terminal trace, or prove a matching terminal label restriction/map. Do not map arbitrary Merkle reads into the old bounded duplex address type. |
| `RawFullPublicSelection`, `RawFullPublicRun`, raw/RWire recorded decoder completion | A after the preceding prefix refactor. Statements at sampler first cells can use prefix/table-before invariance; old whole-log helper cannot simply be reused. |
| `R19BudgetSamplerReads` | A: samplers unchanged. |
| `R19BudgetOriginalReads.verifier_queries`, `verifier_reads`, `original_reads` | B: terminal reads must be counted. New sufficient theorem: decision issued calls ≤ B and `561 + B ≤ 1161`. An arbitrary dO has no uniform budget. |
| `DecoderQueryAccounting.verifier_starts_le_33`, `recorded_starts_le`; `BinHonestQueryBudget.verifier_starts`, `recorded_starts` | B: add terminal **decoder starts**, separately from raw query count. The actual unconditional BIN bound is 34, not the older conditional 33 (`HonestRowStarts`). To retain Q+34 prove terminal Merkle queries are rejected by the start decoder (or already read). A larger raw-read allowance alone does not prove this. |
| `AcceptedAdaptiveFiatShamir`, `RawRecordedOracleExtractionMassBin`, `RawRecordedActualAdaptiveFailureBoundBin`, binary collision/density/first-hit bounds | A: already quantify over arbitrary V/programs or traces. Re-establish budget, completion, chain reads and terminal semantic premises for the new instance. |
| `RawChecksAdaptiveCleanModelBin`, `RawChecksAdaptiveFailureNoModelBin` | A conditional: replay, chain inclusion and extractor word alignment transport; acceptance-implies-Checks remains an obligation of a constructed decision. |
| `RawRecordedLogLengthBin.compiled_log_length` | A: log = original log + full verifier replay, including repeated terminal queries. First-read preservation does not remove this suffix. |
| `RawExtractorCostComposedBin.LedgerRefinement`, `accepted_attempt_cost`, `accepted_attempt_polynomial`, M10 recorded extractor cost | A: extractor/run types and their explicit log-length premise are unchanged; establishing that premise is B. Larger log length changes the concrete cost envelope/instantiation. No instrumentation files changed. |
| `R16CanonReduction.verifier_congr`, `original_canon`, `R16CanonRecorded.compiled_observations`, d₀ schedule admission | A: erasure still identifies decision programs; use evaluated terminal output for accepted-run projections. Malformed schedule rejection must still be constructed. |
| C3/R19/R-wire/R9 wrappers and `RecordedBinaryExperimentBin` R-premise definitions | A conditional: thread the program-valued decision through original/compiled runs and all premises; generic soundness composition survives. This study does not port or discharge these endpoint theorems. |

A = unchanged mathematical fact after the type/API port; B = numerical or
log-size statement needs explicit terminal accounting; C = old full-log claim
is false without a changed statement. The inventory applies this assessment
to each matched declaration, including unaffected generic arithmetic helpers.

## 3. Generic-depth Merkle prototype

To be completed with checked recovery, operational read containment and limits.

## 4. Budget, cost, risks and acceptance decision

To be completed with the port estimate and explicit remaining obligations.

## 5. Verification and signature accounting

No premise is removed or replaced from any existing theorem signature. The
endpoint signature diff is empty: no before/after deletion is claimed. Prototype
lemmas have their own explicit assumptions; they are not premise removals from
R19. In particular collision exclusion remains necessary.
