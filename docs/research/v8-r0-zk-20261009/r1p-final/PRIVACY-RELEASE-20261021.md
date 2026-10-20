# Release privacy composition — 2026-10-21

Branch `codex/cx-builder-ref5-20261021`, base `b89c4bae8`.

## Proved endpoint

`R1Z.PrivacyR1FinalRelease.privacy_R1_release` composes the D94 history
reduction with the D96 canonical-builder reduction. It specializes `h` to
`BuilderSource.prover (K := WideExact)`. For each honest witness, public base
membership follows from its public projection, and builder soundness follows
from `BuilderProtocolInstance.builder_sound`. It calls D94; neither privacy
reduction is reproved. Its witness-independent numeric component composes
D96's `BuilderProtocolBounds.error_bound` with D94's fresh-budget lemmas.
No witness-existence assumption is introduced to prove a numeric bound.

Writing `W` and `Pr` for the constructed protocol and `q = 8*n1 W Pr + 1`,
the conclusion is exactly D94's:

```
ZK_FSS … (modelError W Pr L₁ L₂ + 16/2^486 + freshBudget q)
modelError W Pr L₁ L₂ + 16/2^486 + freshBudget q
  ≤ 2^-109 + 2^-137 + 2^-454 + freshBudget q
modelError W Pr L₁ L₂ + 16/2^486 + freshBudget q < 2^-100
```

This is a protocol-model endpoint conditional on the execution joins below.
It is not yet a frozen-Rust privacy theorem or an inhabitant of RustRuntimeJoin.
`PrivacyR1Final.lean` and both predecessors are unchanged.

## Signature audit

Run `python3 r1p-final/release-audit.py` from the research directory.
`release-signature-audit.json` pins all three source files and records each
binder. Against D94, exactly `hpub` and `builder_refinement_D46_D51` are
removed after the displayed specialization; every other binder and the whole
conclusion are identical modulo whitespace and `(h).` projection notation.
Against D96, all common binders except the two execution joins are identical.
Those two use exactly D94's `ModelExecutionJoin` on its fixed real/ideal bad
events, replacing D96's `ScanCoupling`. D94 proves the model mass bounds;
there is no arbitrary-event assumption and no real history-law premise.
D96's smaller error is enlarged by D94's proved freshness allowance.

## Remaining premises and owners

The data `base`, `F`, `B`, `outputs`, `x`, `seed`, `cF`, `L₁`, `L₂`,
`source`, and `observer_program` are universally quantified choices. The
endpoint fixes the canonical builder and chooses public width from the exact
public-byte length. Source correspondence for these choices is still owed.

| Premise | Plain-English meaning | Owner |
|---|---|---|
| `hB` | The selected packing basis satisfies PackField. | Packing / lead |
| `R_commit_equal_fibres` | Every full tape has exactly cF preimages under the actual finite random-carrier adapter. Zero-fill is insufficient (D95). | Prover commitment / sampler owner |
| `R_commit_exhaustion` | The finite two-stream sampler has the declared exhaustion guarantee. | Prover commitment / sampler owner |
| `R_commit_counter₁`, `R_commit_counter₂` | Both expander counters fit the 64-bit grammar. | Prover commitment / caller owner |
| `R_commit_stream₁`, `R_commit_stream₂` | Enough expander bytes cover both declared tape streams. | Prover commitment / caller owner |
| `R_wire_coin_carrier` | Commitment coins and indexed oracle answers have the declared bijection. | Prover commitment / carrier owner |
| `R_wire_D80_batches` | Source batches normalize to the model's indexed commitment batches. | Commitment wire / caller owner |
| `R_wire_D80_ordered_log` | The ordered commitment log is exactly the grammar/open-list log for all specified witnesses, tapes, roots, answers and challenges. | Commitment wire / ordered-log owner |
| `R_commit_cell_count` | The two tape lengths meet the frozen cell-count accounting. | Prover commitment / count owner |
| `R_commit_blocks₁`, `R_commit_blocks₂` | Each expander uses at most twice its corresponding tape length in blocks. | Prover commitment / count owner |
| `Fintype source.RealRand`, `Nonempty source.RealRand` | Real source coins have a finite nonempty uniform carrier. | Real experiment / runtime owner |
| `Fintype source.IdealRand`, `Nonempty source.IdealRand` | Ideal source coins have a finite nonempty uniform carrier. | Simulator / runtime owner |
| `R_wire_builder_checker_D75_retry` | For every observer and honest witness with the selected public statement, source and model real executions join off D94's fixed parser/lazy bad event. Includes actual checker, retries, errors and publication. | Builder / real runtime worker (this task; open) |
| `G_sim_R_wire` | For every observer, source and model ideal executions join off the fixed selected-history bad event. | Simulator / history source owner |

Removed premises and their owners: builder soundness is discharged for the
canonical builder by D96; public base membership is derived per witness;
real and ideal model-history mass laws are discharged by D94 and D91.
The remaining execution joins are not consequences of builder soundness.

## Focused validation

`release-attempts.jsonl` retains every attempt, exact source revision and SHA,
direct-import fingerprint, full compiler output and time receipt.
Attempts 9226/9227 failed on notation/import mistakes; no failed axiom audit
is accepted. Corrected-source attempt 9228 passes: exit 0, 8.28 seconds,
4,131,244 KiB peak RSS, 0 swaps. Axiom result:

```
'R1Z.PrivacyR1FinalRelease.privacy_R1_release' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The task-owned copy of run-joint.sh retains env J, attempt allocation,
reservation checking and slot locking; its scope uses MemoryHigh=6G,
MemoryMax=8G, MemorySwapMax=0, TasksMax=64. The shared launcher is unchanged.
No shipped Rust file changed in this stage; no ELF rebuild is required.

## Bank std-model stage

D96's rejected all-copy-crates bank extraction is now usable as an axiom-free
Lean definition: `R1Z.BuilderBankExtracted`. `adapt-bank.py` pins the raw file
and makes only the inventoried adaptations in `bank-adaptation.json`:

- Supply `array.from_fn`, iterator map construction/next, and both range
  membership functions from `BuilderStdModels`. Mutable closure state is
  threaded in increasing-index order; None never calls the map closure;
  comparisons short-circuit. Inclusive membership treats exhausted ranges
  according to the pinned Rust RangeBounds implementation (exclusive end).
- Remove the generated map/collect dictionary fields absent from the pinned
  backend Iterator record. The caller already invokes their standalone
  defaults explicitly; next and its closure/iterator arguments are retained.
- Define the extracted core-field constant as its literal source value,
  `2147483647#u32`.
- Adapt two shift-count types to the pinned backend: `BuilderStdShift` proves
  that truncating a usize count to u32 preserves its residue modulo 64;
  literal 1i32 becomes 1u32. No admitted-domain bound is needed for that cast.

The bank's complete `merged_banks` definition compiles and audits to only
`propext`, `Classical.choice`, `Quot.sound` (9235; exit 0, 6.50 seconds,
2,677,024 KiB peak RSS, 0 swaps). It contains no opaque source declaration.
`bank-source-check.json` verifies 173 current source pins: all inherited
core/statement .rs/.toml pins and all three copy-crate source files.
No Rust source was modified and no new extraction success is claimed.

`BuilderStdCollect` additionally proves the pinned Vec iterator collector
preserves any finite next-result trace, including the pure map adapter's
order. It uses symbolic induction, never enumerates 57 blocks or 16,384 bank
cells. The five adapters have 9 checked specification theorems (9231), the
shift adapter 3 (9234), and collection 3 (9238). Full per-attempt receipts,
including failures and corrected sources, are in `release-attempts.jsonl`.

This stage clears unsupported std declarations, not the remaining
whole-bank equivalence theorem: the extracted Parts/loop/writer outputs
still need pointwise identification with `R0Z.WriterRefine.copyCellMerged`.
The raw mapper and full public projection also still need to be joined to
successful compiler executions. RustRuntimeJoin is not claimed inhabited.

## Extracted-call bridges and isolated source obstruction

`BuilderBankShape` proves the actual extracted `late_row`, `node_kind` and
`zero_kind` dispatch predicates against their mathematical intervals, using
standard usize comparison specifications. `BuilderStdArray` proves the
bounded-index array adapter at one fixed closure state, and
`BuilderBankArray.digest8` applies it to the actual extracted closure, proving
its output equals the existing `WriterRefine.digest8`. These are symbolic
proofs about all inputs, with no finite table normalization.

| Focused final target | Attempt | Exit | Wall | Peak RSS KiB | Swap |
|---|---:|---:|---:|---:|---:|
| `R1Z.BuilderBankShape` (5 theorems) | 9243 | 0 | 2.06 s | 3,717,912 | 0 |
| `R1Z.BuilderStdArray` (3 theorems) | 9244 | 0 | 1.22 s | 2,536,200 | 0 |
| `R1Z.BuilderBankArray.digest8` | 9247 | 0 | 1.82 s | 3,732,336 | 0 |

To isolate the admission frontier rather than rerun the whole compiler,
`extract-records-focused.py` extracts just the actual Rust `records` function,
with all three copy crates included, in this branch's own capped host
workspace. This is a new, smaller target than D83's whole-compiler run.
Charon passes (exit 0, 10.329 s, 614,304 KiB RSS, zero swap); Aeneas fails
(exit 2, 0.290 s, 81,136 KiB RSS, zero swap):

```
Failure "Unreachable"
Source: crates/aspis-statement/src/pool_v1/pair_forest_copy_builder.rs:230:16-230:117
Compiler source: interp/InterpAbs.ml:1688
```

The failing expression borrows one of the selected pair's two commitment
arrays. `records-focused-evidence.json` contains both full receipts, full
translation failure, exact command, source revision `4b44a9495`, verified
current source pins, tool pins, and LLBC SHA/size. LLBC and compiled artifacts
remain on the host. Both scopes have MemoryHigh=6G, MemoryMax=8G,
MemorySwapMax=0, TasksMax=64, four Cargo jobs and the requested RUSTFLAGS.
This is a translation failure, not a memory failure; it was not rerun.
The prior owned-record Kani certificates remain applicable component evidence;
they do not by themselves give a successful-compiler semantic relation proof.

## Final status and exact handoff

Part 2 is proved for the canonical protocol instance. Part 1 is **not closed**.
The direct source route still fails at the isolated records borrow above.
The reference route still needs the following proofs; this report does not
claim that those mathematical obligations are impossible:

| Obligation | Exact next work | Owner |
|---|---|---|
| Successful-source admission | Relate successful shipped compile inputs/outputs to the same raw RW/RP and semantic public projection; derive WitnessOk, PubCorr, embedded RspendPlus (including append/carry and the change sentinel). | Builder source worker / lead |
| `RustRuntimeJoin.raw_trace_eq` | Use the now-compiled bank definition to prove Parts/57-block materialization, recursive callee refinements, bank-fill loop, merge and final Vec/column-wrapper equality with copyCellMerged. Dispatch and digest8 are proved here; whole-bank equality is not. | Builder source worker |
| Concrete `RustRuntimeJoin` | Define the shipped successful-source HonestProver domain and fill all fields from the above results, existing mapper/empty-root certificates, and S2 transport. An instance subtype carrying RspendPlus would assume the admission being requested and is not supplied. | Builder source worker |
| Real checker/retry `ModelExecutionJoin` | Refine actual checker-input construction, P_chk/P_R1, no-pole/VR1, mask tape, retries, errors, publication/serialization and oracle history to D94's fixed-event experiment. Builder trace validity alone gives neither a coupling with uniform marginals nor off-event observation agreement. | Real runtime worker |

No source h or source FSExperiments is silently defined to equal the model.
No execution join is discharged by choosing arbitrary exception events.
No successful-source admission, shipped RuntimeJoin inhabitant, or real
checker/retry coupling is claimed.

`release-final-audit.py` verifies all eight new current modules, every one of
25 theorem audits, the bank definition audit, current source hashes, retained
successful receipts, and unchanged direct dependency objects. It also
verifies no shipped crate file changed against `b89c4bae8`. The resulting
`release-final-audit.json` records resolved import object SHA/size and the
env-J/launcher pins. Every final audit uses only a subset of propext,
Classical.choice and Quot.sound. Failed elaborations remain in the JSONL
and are excluded from final evidence. No frozen-manifest replay, SBF rebuild,
merge or push is claimed; no frozen or shipped source changed.

## D99 continuation 6: source-facing endpoint and exact signature difference

`PrivacyR1FinalReleaseSource.privacy_R1_release_source` is a conditional
source-facing generalization with the same freshness allowance and <2^-100
conclusion. The original canonical release theorem is unchanged. The new
endpoint takes an arbitrary honest prover h and an explicit
`R_source_records_admission_banks_transport : RustRuntimeJoin h`.
No inhabitant of that join for shipped Rust is claimed.

**No remaining D99 release premise is deleted by continuation 6.** The exact
real `ModelExecutionJoin` and ideal `ModelExecutionJoin` binders stay
verbatim, as do all commitment premises and the entire conclusion. The new
record and bank proofs narrow implementation obligations, but do not imply
those execution joins. This is not presented as an assumption reduction:
h was fixed to the canonical builder before, and is an input afterwards.
The checked assembly of builder soundness/public membership from RuntimeJoin
is reused from D96; it is not newly asserted to identify the shipped source.

`builder-cont6-signature-audit.py` checks that deleting only the displayed
new binder and restoring the theorem name reproduces the old statement
byte-for-byte. It records the h-context change separately. Before context:
`local notation "h" => (BuilderSource.prover («K» := K))`.
After context: `(h : HonestProver K)`.

The new `BuilderExecutionBoundary.no_constant_mismatch_join` proves that
constant-zero and constant-one observations cannot admit a fixed-event
ModelExecutionJoin when the model bad-event union has mass <1. Thus deleting
the real execution premise for an arbitrary `source : FSExperiments` cannot
follow from builder soundness alone. This is an obstruction to that generic
inference, not a counterexample to privacy of the shipped prover.

The actual remaining source obligations are: successful forest semantic
admission (the isolated higher-ranked callback lifetime blocks the direct
translation route); Parts content equal to the canonical writer composition;
final Vec/column wrapping and the concrete source h/transport; and actual
checker/no-pole/tape/retry/error/publication/serialization/oracle-history
execution with the required uniform coupling. See
`BUILDER-CONT6-20261021.md` and `builder-cont6-extraction.json` for the exact
proved boundary, source pins and retained failures. Neither arbitrary bad
events nor a source experiment defined equal to the model is used.

Verbatim before statement (in the fixed canonical-h context):

```lean
theorem privacy_R1_release
    (seed : R1ProverP K CommitHandle Aux F
      (wire base ((base.pubBytes x).length) h B outputs x).toWire)
    (hB : R0Z.K4.PackField B)
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

Verbatim after statement (in the arbitrary-h context):

```lean
theorem privacy_R1_release_source
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
