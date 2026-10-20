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
