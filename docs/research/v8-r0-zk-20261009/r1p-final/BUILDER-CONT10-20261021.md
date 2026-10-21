# Builder continuation 10

Branch `codex/cx-builder-ref10-20261021`, base `e5d6d81a5`.

## Stage 1: destructor field composition

`BuilderDropFields` composes the existing projected volatile-word contract
at byte granularity. `word_bytes` and `column_bytes` identify exact half-open
byte intervals; `word_frame`, `column_frame`, `frame_compose`, `fields_frame`
and `fields_observation` cover arbitrary word counts, initial bytes and lists
of fields (in particular the sixteen Vec columns). No disjointness between
columns is needed for the frame result; retained output must be disjoint from
the union of buffers. J9378: exit 0, 1.39 s, peak 2,537,168 KiB, zero swaps;
nine allowed-axiom audits. J9377 was an elaboration failure corrected by
closing a definitional equality; no resource failure or cap increase.

No whole-frame Kani check or unchanged store check was rerun. The existing
57-check projected store certificate is inherited. The new theorem composes
its write-set shape for arbitrary lengths. Actual pointer-to-byte enumeration,
iterator traversal and allocation/deallocation semantics remain source
correspondence obligations; the model theorem alone is not that certificate.

`BuilderDropStoreComposition` strengthens stage 1: its input is an arbitrary
store satisfying the projected word write-set contract. A word-list induction
then a field-list induction derive the complete destructor frame and retained
output rule, without equating that store to the concrete `wipe`. J9390: exit 0,
1.25 s, 2,532,776 KiB, zero swaps; four allowed-axiom audits. Rust pointer and
iterator correspondence remains the source boundary described above.

## Stage 2: forest standard library and validator

All 24 std externals have explicit adapters in `BuilderForestStdPort`.
`BuilderForestStd` adds 27 checked specifications covering array iteration,
mutable array mapping, lazy flattening (including empty inner iterators),
short-circuit iterator any, sequential checked u64 accumulation, Option/Result
branching/mapping, and positive-size slice chunking with exact head/tail
contents. Existing proved adapters supply from_fn, map-next, ranges and slice
any. No std external is an axiom. J9380/J9382: 1.66/1.24 s,
2,549,788/2,542,296 KiB, zero swaps. The port inventory distinguishes these
24 declarations from three opaque Aspis functions: external_linear_lazy,
records and Drop. No opaque source declaration is silently supplied by a std
model.

Three projected Kani harnesses replace the timed-out whole-tree comparison:
frontier transition 307 checks (three unreachable), index guard 74 checks,
and root branch 329 checks (three unreachable). All pass; 5.824/4.407/6.482 s,
620,716/604,440/623,180 KiB, zero swaps. These are projected expressions,
not calls to the whole shipped validator. The frontier arrays are projected
to one arbitrary node/empty pair; the root helper to one arbitrary common
pure result. Full bytewise/source pins, commands, limits and logs are in
`builder-cont10-host-evidence.json`.

`BuilderForestValidatorExtracted` dependency-slices the actual generated
validator. The unchanged root reconstruction call becomes an explicit pure
function parameter. There are no opaque declarations in this slice. J9387:
exit 0, 1.31 s, 2,544,424 KiB, zero swaps, two allowed-axiom audits.
`BuilderForestValidatorSteps.complete_frontier` proves its entire carried
loop equals the early-return scan by induction on symbolic remaining length.
It preserves errors, stops at the first bad step and does not enumerate twenty
concrete cells. J9391: exit 0, 1.97 s, 4,011,288 KiB, zero swaps, five
allowed-axiom audits. No whole-frame or timed-out whole-validator job reruns.

The aggregate port J9383 exposed a distinct backend-interface obstruction:
raw Aeneas emits mutable callback borrow-back closures, whereas env J expects
(output,state) pairs. Errors include hash_fields_with_trace, permute callbacks
and the curried nullifier callback. It is rejected, not an admission certificate.
Dependency slicing removes unrelated callbacks for the focused validator;
it does not repair the full forest caller. Earlier failed edits and missing
object J9386 remain in the attempt receipts. Only successful matching hashes
and dependency fingerprints count as proofs. `BuilderForestValidatorAcceptance.validator_success` derives successful
execution of all twenty actual projected checks from successful whole-wrapper
execution, for every supplied pure root function. J9394: exit 0, 1.87 s,
4,010,620 KiB, zero swaps, four allowed-axiom audits.

The strengthened root harness also covers all thirteen tree-error variants:
331 checks (three unreachable), 3.703 s, 523,324 KiB, zero swaps. Its earlier
329-check result remains supplemental; the changed harness was checked once.

Complete semantic admission
(RspendPlus, append/public/empty-root correspondence and sentinel) is still
not established by these validator control-flow facts.

## Stage 3: shipped runtime inhabitant — blocked by source admission

The exact `RustRuntimeJoin` was checked against its actual definition. It
requires the same source instance's `publicInput`, raw witness/public records,
`WitnessOk`, `PubCorr`, embedded `RspendPlus`, public equality, raw trace equality
and S2 transport equality. This stage does not construct it.

The new validator theorem supplies only the actual frontier-check sequence.
Neither that result nor std totality supplies successful forest caller
admission, digest-check identity, append/root/carry semantics, D50's sentinel,
or the source instance/public map. The raw aggregate cannot currently be used
as the missing evidence: J9383 records concrete ill-typed callback interfaces,
and the records/Drop source declarations remain opaque outside the focused
slice. Silently choosing callback outputs would change the caller semantics.

There is also an already checked type-level obstruction to deleting the join
at the inherited arbitrary-h endpoint: `BuilderRuntimeBoundary.zero_padding`
forces all padding columns to zero, while
`BuilderRuntimeBoundary.no_mismatch_runtime_join` rules out the unit-instance
constant-one prover. Parts content and validator results do not constrain
that arbitrary h. Replacing this with a canonical prover or a subtype assuming
RspendPlus would not construct the shipped inhabitant. These existing targets
were not rerun unchanged. No runtime binder is removed.

This is an explicit unsuccessful stage, not a claim that the shipped compiler
violates its intended relation. Next concrete source target is the forest
caller with sound callback state threading, followed by semantic admission
and the successful compiler's actual instance/public projection.

## Stage 4: checker/retry coupling and Source5

The checker/retry coupling is not constructed. Its actual type quantifies over
arbitrary `FSExperiments`, observer programs, randomness and source h, and
asks for agreement outside the fixed model events. Builder/validator facts
supply no law relating those observations. The inherited checked
`BuilderExecutionBoundary.no_constant_mismatch_join` rules out zero-versus-one
observations whenever the fixed bad-event union has mass less than one.
This prevents an unconditional inference from the new builder facts; it is
not an assertion of a defect in shipped execution.

The missing concrete law must cover the exact P_chk/P_R1 checker inputs,
pole/VR1 checks, masks, retries, next_attempt failures, non-Rejected aborts,
publication/serialization and reached-query history. The full forest callback
port is a prerequisite for the requested source instance; it is not an
execution law. No bad event is broadened, no arbitrary observation replaced,
and no execution premise renamed into another assumed package.

`PrivacyR1FinalReleaseSource5` builds on Source4 and imports the new field/store
composition, std port and projected validator acceptance results. Every
inherited binder and the complete error/freshness/strict-bound conclusion
is preserved. The exact signature audit below has zero deletions and zero
additions. It is deletion-only but not strictly weaker, and is not a completed
shipped-source privacy release.

## Final verification and resource record

The read-only final audit validates eight current modules, 52 complete named
axioms results, exact source hashes and current direct-import object
fingerprints. Accepted axiom sets are subsets of propext, Classical.choice and
Quot.sound; all accepted attempts have zero swaps. The source revisions,
dirty flags, commands, wall/RSS/swap and full failure/replacement logs are in
`builder-cont10-attempts.jsonl` and `builder-cont10-final-audit.json`.

| Target in R1Z | attempt | exit | wall | peak RSS KiB |
|---|---:|---:|---:|---:|
| `BuilderDropFields` | 9378 | 0 | 0:01.39 | 2537168 |
| `BuilderDropStoreComposition` | 9390 | 0 | 0:01.25 | 2532776 |
| `BuilderForestStd` | 9380 | 0 | 0:01.66 | 2549788 |
| `BuilderForestStdPort` | 9382 | 0 | 0:01.24 | 2542296 |
| `BuilderForestValidatorExtracted` | 9387 | 0 | 0:01.31 | 2544424 |
| `BuilderForestValidatorSteps` | 9391 | 0 | 0:01.97 | 4011288 |
| `BuilderForestValidatorAcceptance` | 9394 | 0 | 0:01.87 | 4010620 |
| `PrivacyR1FinalReleaseSource5` | 9395 | 0 | 0:03.38 | 4123624 |

`builder-cont10-p6-audit.json` checks four projected solver receipts and all
current shipped .rs/.toml pins. It reconstructs the sole root-error-selector
tail change for the first three input-tree hashes; frontier/index harness
bodies are unchanged. Per-run Rust source manifests were captured before
launch. Tool/lock hashes in that audit are explicitly sampled after the runs.

All builds used the requested scopes, MemoryHigh=6G, MemoryMax=8G,
MemorySwapMax=0, TasksMax=64; Rust used four jobs and the required linker flag.
Both adapter generators pass their deterministic --check. No full frozen
manifest replay or complete source-release verification is claimed. No
unchanged full regression or stopped whole-frame/whole-validator job reran.
New module names only: no pre-existing shared module/object was replaced.

No shipped crate/program file changed against e5d6d81a5, so the ELF rule is
not triggered; inherited frozen pins are not presented as new measurements.
All original privacy, Source1–4, RuntimeJoin and concurrent-worker modules
are unchanged. No binary, object, LLBC, archive or key is committed. No
wallet operation, key cleanup, push or merge is performed. No task-owned
build is left running.

Open: actual pointer/iterator correspondence for the destructor; full forest
callback-state port and semantic admission; the shipped runtime inhabitant;
and the concrete checker/retry/observer execution laws. The new projected
frame and validator theorems do not silently discharge those source joins.

## Verbatim endpoint signature audit

No complete runtime or execution join was discharged. The binder/conclusion
diff is empty, excluding the theorem name: deletion-only with zero deletions,
not a strict weakening. No new or stronger premise is introduced. The error,
freshness term and strict <2^-100 conclusion are byte-identical.

Before, verbatim:

```lean
theorem privacy_R1_release_source4
    (seed : R1ProverP K CommitHandle Aux F
      (wire base ((base.pubBytes x).length) h B outputs x).toWire)
    (hB : R0Z.K4.PackField B)
    (R_source_records_admission_banks_transport : BuilderRuntimeJoin.RustRuntimeJoin h)
    (cF : ℕ)
    (R_commit_equal_fibres : ∀ τ : Tape K F, (Finset.univ.filter
      (fun e : (Fin ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₁ → OracleAnswer) × (Fin ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₂ → OracleAnswer) =>
        ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).tapeOf e.1 e.2 = some τ)).card = cF)
    (L₁ L₂ : ℕ) (R_commit_exhaustion : RExh (prover base ((base.pubBytes x).length) h B outputs x seed).toProver L₁ L₂)
    (R_commit_counter₁ : ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₁ ≤ 2^64) (R_commit_counter₂ : ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₂ ≤ 2^64)
    (R_commit_stream₁ : 16 * L₁ ≤ ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₁ * 8) (R_commit_stream₂ : 16 * L₂ ≤ ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₂ * 8)
    (R_wire_coin_carrier : ((wire base ((base.pubBytes x).length) h B outputs x).toWire).Cm ≃ (RIdx → OracleAnswer))
    (R_wire_D80_batches : RWireBatches (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver)
    (R_wire_D80_ordered_log : ∀ (w : (h).Instance) (sec : SecP) (d : OracleAnswer)
      (τ : Tape K F) (roots : Fin 3 → OracleAnswer) (rest : RIdx → OracleAnswer) (ch : Challenges K),
      ((wire base ((base.pubBytes x).length) h B outputs x).toWire).comLog (R_wire_coin_carrier.symm rest) roots (view h B outputs x w ch τ) ch =
        (((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).openList ch).map (fun c =>
          (gram (((wire base ((base.pubBytes x).length) h B outputs x).toWire).pubBytes x) ((wire base ((base.pubBytes x).length) h B outputs x).toWire).vtag (((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).leafVal h w x τ ch) sec d rest
            (cposOf (E₁ := ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₁) (E₂ := ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₂) c), ansC roots rest c)))
    (R_commit_cell_count : RCommitCount L₁ L₂)
    (R_commit_blocks₁ : ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₁ ≤ 2 * L₁) (R_commit_blocks₂ : ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₂ ≤ 2 * L₂)
    (source : FSExperiments K CommitHandle Aux R1Bat F)
    [Fintype source.RealRand] [Nonempty source.RealRand]
    [Fintype source.IdealRand] [Nonempty source.IdealRand]
    (observer_program : source.Adversary → View K CommitHandle Aux R1Bat →
      List (List UInt8 × OracleAnswer) → OProg)
    (R_wire_builder_checker_D75_retry : ∀ (adv : source.Adversary) (w : (h).Instance),
      (h).public w = x.1 → ModelExecutionJoin
        (realTest h B outputs source adv x w)
        (realTest h B outputs (fsR1P (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver 8 (by decide)
          (P_R1 (h).transport B hB) (fun h' => VR1 h')) (RomObserverBin.observerMap source observer_program adv) x w) (QueryScanRealLazyBound.realBad (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver 8 h B outputs x w))
    (G_sim_R_wire : ∀ adv : source.Adversary, ModelExecutionJoin
      (idealTestS source adv x (simE (h).transport B outputs x))
      (idealTestS (fsR1P (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver 8 (by decide) (P_R1 (h).transport B hB) (fun h' => VR1 h'))
        (RomObserverBin.observerMap source observer_program adv) x (simE (h).transport B outputs x)) (QueryScanIdealHistory.selectedBad)) :
    ZK_FSS h B outputs source x (simE (h).transport B outputs x)
      (modelError (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver + 1)) ∧
    modelError (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver + 1) ≤
      1 / 2^109 + 1 / 2^137 + 1 / 2^454 + QueryScanFreshUnion.freshBudget (8 * n1 (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver + 1) ∧
    modelError (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver + 1) < 1 / 2^100
```

After, verbatim:

```lean
theorem privacy_R1_release_source5
    (seed : R1ProverP K CommitHandle Aux F
      (wire base ((base.pubBytes x).length) h B outputs x).toWire)
    (hB : R0Z.K4.PackField B)
    (R_source_records_admission_banks_transport : BuilderRuntimeJoin.RustRuntimeJoin h)
    (cF : ℕ)
    (R_commit_equal_fibres : ∀ τ : Tape K F, (Finset.univ.filter
      (fun e : (Fin ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₁ → OracleAnswer) × (Fin ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₂ → OracleAnswer) =>
        ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).tapeOf e.1 e.2 = some τ)).card = cF)
    (L₁ L₂ : ℕ) (R_commit_exhaustion : RExh (prover base ((base.pubBytes x).length) h B outputs x seed).toProver L₁ L₂)
    (R_commit_counter₁ : ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₁ ≤ 2^64) (R_commit_counter₂ : ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₂ ≤ 2^64)
    (R_commit_stream₁ : 16 * L₁ ≤ ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₁ * 8) (R_commit_stream₂ : 16 * L₂ ≤ ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₂ * 8)
    (R_wire_coin_carrier : ((wire base ((base.pubBytes x).length) h B outputs x).toWire).Cm ≃ (RIdx → OracleAnswer))
    (R_wire_D80_batches : RWireBatches (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver)
    (R_wire_D80_ordered_log : ∀ (w : (h).Instance) (sec : SecP) (d : OracleAnswer)
      (τ : Tape K F) (roots : Fin 3 → OracleAnswer) (rest : RIdx → OracleAnswer) (ch : Challenges K),
      ((wire base ((base.pubBytes x).length) h B outputs x).toWire).comLog (R_wire_coin_carrier.symm rest) roots (view h B outputs x w ch τ) ch =
        (((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).openList ch).map (fun c =>
          (gram (((wire base ((base.pubBytes x).length) h B outputs x).toWire).pubBytes x) ((wire base ((base.pubBytes x).length) h B outputs x).toWire).vtag (((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).leafVal h w x τ ch) sec d rest
            (cposOf (E₁ := ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₁) (E₂ := ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₂) c), ansC roots rest c)))
    (R_commit_cell_count : RCommitCount L₁ L₂)
    (R_commit_blocks₁ : ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₁ ≤ 2 * L₁) (R_commit_blocks₂ : ((prover base ((base.pubBytes x).length) h B outputs x seed).toProver).E₂ ≤ 2 * L₂)
    (source : FSExperiments K CommitHandle Aux R1Bat F)
    [Fintype source.RealRand] [Nonempty source.RealRand]
    [Fintype source.IdealRand] [Nonempty source.IdealRand]
    (observer_program : source.Adversary → View K CommitHandle Aux R1Bat →
      List (List UInt8 × OracleAnswer) → OProg)
    (R_wire_builder_checker_D75_retry : ∀ (adv : source.Adversary) (w : (h).Instance),
      (h).public w = x.1 → ModelExecutionJoin
        (realTest h B outputs source adv x w)
        (realTest h B outputs (fsR1P (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver 8 (by decide)
          (P_R1 (h).transport B hB) (fun h' => VR1 h')) (RomObserverBin.observerMap source observer_program adv) x w) (QueryScanRealLazyBound.realBad (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver 8 h B outputs x w))
    (G_sim_R_wire : ∀ adv : source.Adversary, ModelExecutionJoin
      (idealTestS source adv x (simE (h).transport B outputs x))
      (idealTestS (fsR1P (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver 8 (by decide) (P_R1 (h).transport B hB) (fun h' => VR1 h'))
        (RomObserverBin.observerMap source observer_program adv) x (simE (h).transport B outputs x)) (QueryScanIdealHistory.selectedBad)) :
    ZK_FSS h B outputs source x (simE (h).transport B outputs x)
      (modelError (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver + 1)) ∧
    modelError (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver + 1) ≤
      1 / 2^109 + 1 / 2^137 + 1 / 2^454 + QueryScanFreshUnion.freshBudget (8 * n1 (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver + 1) ∧
    modelError (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (wire base ((base.pubBytes x).length) h B outputs x).toWire (prover base ((base.pubBytes x).length) h B outputs x seed).toProver + 1) < 1 / 2^100
```
