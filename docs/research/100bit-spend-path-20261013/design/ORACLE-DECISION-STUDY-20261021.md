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
d₀ helpers; local transitive imports comprise 460 modules, including historical
helper imports, with 73 textual pure-signature modules. The 726 matched lines
span 373 declarations. This is a textual audit, not a kernel dependency claim;
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

`OracleDecisionFeasibilityMerkle.checkPath path leaf root` runs the existing
`BinMerkleProgram.leafProgram` and compares the computed digest with `root`.
`decision` places this program at the erased terminal interface. The path,
leaf and root are explicit parameters: this is a checking primitive, not a
parser that locates the real opening in erased protocol messages.

Checked results, for an arbitrary slot list (hence symbolic depth):

* `eval_check` preserves the opening-program log exactly; comparison adds no
  oracle calls.
* `path_trace_length` and `check_queries` give exactly depth + 1 issued calls,
  including the leaf hash. A depth-18 path costs 19 calls.
* `opening_reads` places every opening read in the full prover/sampler/decision
  experiment. There is no caller-supplied read-containment hypothesis.
* `accepted_root` obtains actual opening success from experiment acceptance.
* `accepted_leaf_determined` applies existing binary causal cut recovery using
  these operational facts. It recovers `some (packed, salt)` from the recorded
  log strictly before the first committed-root frame.
* `recorded_log` identifies that trace with the self-recorder's returned log.

`OracleDecisionFeasibilityBridge` additionally proves
`opening_reads_compiled` and `compiled_leaf_determined` for the **actual
compiled experiment shape**, with arbitrary `buildWords`. Thus recovery is
not confined to a detached toy log or to the self-recording wrapper.
`single_path_budget` proves the existing total first-read envelope for one
path of depth ≤599 (including depth18), given the adversary issued-query bound.

Remaining hypotheses are explicit: the committed frame was read; one of the
five existing parsers extracts the claimed root from it; packed width and salt
length are correct; the first-read budget holds; the existing
`AllAddressCollision.bad iv BinRawByteCollisionTargets.pred Q` event did not
occur. Consistency follows from actual program execution. The strengthened
prototype supplies neither a free success premise nor a free opening-read
containment premise. It does not remove any endpoint premise.

Contrast `D0OpeningRecoveryObstruction.successful_opening_not_recovered` and
`depth18_counterexample`: the zero oracle admits two different leaves at the
same root even with both opening traces recorded. This experiment also runs
against arbitrary H, but its recovery theorem deliberately requires collision
exclusion. Oracle decisions make the hash reads operational; they do not make
hash functions injective on collision runs. Likewise, the universal typed
metadata obstruction `D0ErasedWordObstruction.no_erased_final_reader` remains
true; only checked openings on clean runs are identified with recovered data.

## 4. Budget, cost, risks and acceptance decision

### Numerical feasibility

The checked coarse budget theorem is `OracleDecisionFeasibilityBudget.queries`:
verifier calls ≤ `561 + B`, where B bounds the terminal decision calls.
`original_reads` retains `Q + 1161` when `561 + B ≤ 1161`. This is enough for
one generic path with depth ≤ 599, and in particular depth 18. **It is not a
proof that the full frozen decision fits.**

Inspection gives a plausible route to the exact existing envelope. The 33
samplers contain 30 ordinary rows (3 calls), the initial row (4), reseed row
(4), and query row (17): `30*3 + 4 + 4 + 17 = 115`. Invalid message cases
reject with fewer reads. These counts are visible in `DuplexSamplers` and
`R19BudgetSamplerReads`; their aggregate **115 bound has not been proved in
these prototypes**. The existing `QvStage1.transcriptBudget` is also 115.
The existing conditional multiproof profiles give 447 batch-A parents and
527 batch-B parents, with 66 leaf calls, totaling 1040 Merkle calls. Adding
three checkpoint and three resume calls gives terminal allowance 1046;
`115 + 1046 = 1161`. This arithmetic explains feasibility but still requires
an actual decision program and source/profile/stop-prefix correspondence.
Naively recomputing 66 independent depth-18 paths issues 1254 calls before
samplers and cannot justify the same issued-query envelope; shared multiproof
work or a separate distinct-read proof is essential.

M9 needs a separate lemma: Merkle/checksum terminal addresses introduce no
fresh *recognised decoder starts*. The unconditional existing sampler bound
is 34 because the reseed row has two starts. With that label exclusion,
`Q + 34` survives; without it the generic safe bound is `Q + 34 + B`.
Changing this coefficient requires redoing the query-normalised numeric
closure. A bound on distinct oracle reads alone does not preserve Q+34.

M10's log-size condition is a second issue. A compiler run records the whole
original verification and then repeats verification externally. If a full
verifier issues at most 1161 calls, the immediate safe log bound is
`Q + 2322`, not `Q + 1161`. A first-read replay lemma does not shorten this
log. Current `h_M10_log_length` must remain explicit unless separately
established; a future port can enlarge the extractor's size envelope and
reprove the resulting constant cost bound, or redesign logging with exact
value correspondence. No such endpoint change is proposed as a premise
weakening here.

### Port estimate

The audit finds 73 modules with textual pure decision signatures in a
460-module local import cone. The whole cone is **not** a rewrite target.
Allow approximately **70–95 modules and 180–280 proof declarations** to
thread the new type through the active binary, canonical, R-wire and source
premise paths, if the historical helpers are retained. Of these, about
**15–30 proofs** need substantive work: terminal evaluation/read inclusion,
sampler-prefix legacy transport, sharper budgets, zero terminal decoder
starts, checked opening-to-word alignment and altered log-size accounting.
The rest are mechanical parameter changes, erasure congruence or unchanged
trace/probability lemmas. This is a source-inspection estimate, not measured
port labour or a promise that all source joins close. A narrow migration that
keeps pure compatibility wrappers should reduce churn.

Suggested order after acceptance:

1. Expose the existing `OracleVerifier` through a byte-decision adapter and
   keep the pure API as `done` lifting. Port compiler/replay/canonical laws.
2. Construct the actual erased-message parser and shared Merkle multiproof
   decision; prove decoded checks, malformed-schedule rejection and
   checkpoint writer composition. Use collision-conditioned statements for
   recovered words, not universal typed-word reconstruction.
3. Prove sampler ≤115, terminal ≤1046, and zero terminal decoder starts;
   settle compiled log length and the M10 envelope before numerical closure.
4. Port binary completion/semantic consumers and endpoint wrappers with
   signature diffs for any genuine premise weakening. Then run one final
   pinned manifest and axioms audit. Re-pin frozen Rust correspondence only
   after the model is settled.

### Risks and user decision

* Terminal-only recomputation moves reads after challenge generation, whereas
  the deployed two-transaction verifier interleaves checks and can stop early.
  Under a fixed total H, moving deterministic work may preserve accepted
  outputs, but literal traces, stopping prefixes, checkpoint state and caller
  reachability need a proved transport, not an assumed log equality.
* dO can branch on oracle answers and can issue arbitrarily many calls. Every
  numerical bound must refer to the constructed decision, with coverage of
  rejection/suspension prefixes, not an arbitrary dO.
* The terminal decision sees erased bytes and H, not the prover's query
  history or compiler-supplied hidden words. Openings must be parsed from
  available bytes; recovered metadata is related by clean-run binding.
* Whole-log bounded-address/canonical proofs are unsuitable for arbitrary
  raw Merkle inputs. Keep sampler-prefix recovery and unrestricted binary
  collision accounting distinct at the API level.
* Frozen-verifier equality, the actual tx1/Pool caller law, pairing backend,
  semantic arithmetic joins, and efficient extractor adequacy remain source
  obligations. This study is not evidence that R3/R13/R14/R15/R16/R9 or M10
  have been discharged.

**Accept** means authorise a compatibility-preserving oracle-decision port
with the budget/start/log criteria above and the concrete frozen decision as
the eventual instance. **Reject/defer** means retain the pure endpoint and
its source premises (with the separately owned clean-run weakening); keep
these prototypes as feasibility evidence. No approval is needed to complete
this study, and no production migration has been performed.

## 5. Verification and signature accounting

No premise is removed or replaced from any existing theorem signature. The
endpoint signature diff is empty: no before/after deletion is claimed. Prototype
lemmas have their own explicit assumptions; they are not premise removals from
R19. In particular collision exclusion remains necessary.


Focused verification used the prescribed Lean 4.32 executable, `-j1 -M4400
-DElab.async=false`, a private `/tmp/codex-cx-oracle-dec-20261021-objects`
overlay, the pinned local search path, the shared mkdir lock and a process
gate. Each target ran separately under `/usr/bin/time -l`. No package build,
large numeral reduction, certificate regeneration or full frozen-manifest
rerun was needed for this study. This is cache-based focused evidence, not a
new clean unified-release claim (the D63 coherence distinction applies).

| Final target | Attempt | Exit | Wall seconds | Peak RSS bytes | Swaps | Axioms audits |
|---|---:|---:|---:|---:|---:|---:|
| `OracleDecisionFeasibilityCore` | 1 | 0 | 5.483 | 3102507008 | 0 | 5 |
| `OracleDecisionFeasibilityCompiler` | 4 | 0 | 9.300 | 3109928960 | 0 | 9 |
| `OracleDecisionFeasibilityBudget` | 3 | 0 | 7.580 | 3643326464 | 0 | 4 |
| `OracleDecisionFeasibilityMerkle` | 1 | 0 | 19.749 | 3624960000 | 0 | 7 |
| `OracleDecisionFeasibilityBridge` | 2 | 0 | 4.008 | 3622174720 | 0 | 3 |

All 28 new theorems have explicit `#print axioms` reports, with only subsets
of `{propext, Classical.choice, Quot.sound}` in their final green attempts.
Every attempt's exact target/argv, source revision, source SHA256, source
snapshot, direct-import paths/SHA256s, dependency fingerprint, exit, wall time,
RSS, swaps, full wrapped axiom lines and diagnostics are retained under
`evidence/oracle-dec-20261021/`; `manifest.json` indexes the receipts.
Revision denotes the Git parent at launch; the exact working source is pinned
by its hash and snapshot, so subsequent stage commits do not obscure the input.
`audit.json`/`audit.py` verify current source equality with green receipts,
current direct-import hashes, all theorem audits and the no-existing-module
change rule without rerunning Lean.

There were ten actual compilations: six successful (including a superseded
seven-theorem compiler checkpoint) and four local elaboration failures.
Compiler attempt 2 needed qualified experiment names; budget attempts 1/2
needed an open-command fix, qualified recursive definition, pair refinement
and projection simplification; bridge attempt 1 needed a list type annotation.
Each repair changed the source before recompiling. Error-recovery `sorryAx`
reports in failed logs are preserved as diagnostics and are not accepted
proofs. Compiler attempt 1 was cancelled before Lean launch while narrowing
the launcher's process match; its prelaunch receipt has null resource fields.
No compile failed for memory, no cap was raised, and all measured swaps were
zero. Final peak RSS across attempts was 3,643,326,464 bytes.

Completed: exact embedding, effectful compiler replay, declared query-budget
condition, full declaration audit, generic-depth leaf recovery and compiled-run
bridge, recommendation and port estimate. Still proposed: the production
migration, concrete decision parsing/multiproof implementation, sharp full
budget, zero terminal decoder starts, the new log-size envelope, and the
remaining source joins. These are follow-on work, not unfinished feasibility
proofs or a claimed endpoint improvement.
