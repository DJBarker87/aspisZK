# Prover commitment continuation 4 — 2026-10-21

Branch `codex/cx-prover-commit4-20261021`, based on `8c69254eb`.
**The shared-oracle component route is checked; the nine complete source
checklist rows are not discharged.** A zero-filled redundant H1 tape
coordinate obstructs equal fibres on the existing full tape carrier.

D92 identifies the byte callback with the model oracle. No SHA-256 property
is assumed or proved. Evidence is collected under
`docs/research/100bit-spend-path-20261013/evidence/prover-commit4-20261021/`.

## Stage 1: shared oracle harnesses

Proof-only modules use one memoised table for both sides, keyed by the
concatenation of hashv slices. New points receive arbitrary 32-byte answers;
repeats receive the stored answer. Collisions remain possible. Capacity and
per-harness query budgets are assertions, not assumptions. Every loop has an
explicit unwind bound and unwinding assertions remain enabled. The initial legacy-output runs are diagnostic only; final structured-output
verification is pending.

## Checklist scope

No complete source row is discharged by the component checks below. The
verbatim before/after inventory is retained at the end.

## Stage 2: oracle-parametric Lean refinement

New module `R1Z.ProverCommitOracleRefinement` proves cache evaluation,
cache extension, arbitrary fresh-answer extension, and the extracted mask
block, source block and private-leaf evaluations for **every** byte oracle.
The oracle is a function of concatenated bytes. The cache extension theorem
permits collisions. No SHA-256 property, independent-word law or source
carrier instance is inferred.

Env J attempt 8144: exit 0, wall 2.24 s, peak RSS 4,015,488 KiB, zero swaps.
All six `#print axioms` lines are in `lean/out-8144.log`: cache theorems use
`[propext]`, extracted callback refinements use
`[propext, Classical.choice, Quot.sound]`. Source SHA, dependency fingerprint,
revision and complete resource/audit receipts are in `lean/attempts.jsonl`.
The existing capped launcher was used, with no shared module overwritten.

## Stage 3: owned reference lowering and final axioms audit

The proof-only `prover_commit_reference` module is enabled by `cfg(kani)` or
`cfg(aeneas_ref)`. It has an owned expander state, byte-exact word extraction
and a 16-try sampler carrying its result. The first reference failed Aeneas's
nested-return prepass (`Option` language-item diagnostic); the carried-result
replacement translates successfully. Both Charon lowerings have
`has_errors=false`; only the successful replacement is adopted. The accepted
LLBC SHA and size are recorded in `reference-llbc.json`. The only external
constant is M31's exact `P = 2147483647`, defined rather than axiomatized.

The three generated modules compile separately in env J 8148–8150. The
scoped discriminant expansion follows the previous continuation and avoids
its global instance-name collision; raw constructor order and 0–4 values
are preserved. New `ProverCommitReferenceSource` proves cached reads ignore
the callback, termination at 16 attempts, and preservation after success
(attempt 8151). These are component properties, not a full tape theorem.

Final audit `R1Z.ProverCommitOracleAudit`, env J **8152**: exit 0, **2.37 s**,
**4,028,280 KiB** peak RSS, **0 swaps**. Its twelve complete axiom lines cover
all eleven new theorems and `privacy_R1_protocol`. Only
`propext`, `Classical.choice`, and `Quot.sound` occur. Attempts 8145/8146 are
rejected proof drafts with a constructor elaboration error; their recovery
`sorryAx` output is not accepted. Final salt refinement passes in 8147.
No existing privacy/source-identification/history module was edited.

## Stage 4: final shipped-source ELF gate

All shipped-file additions are proof-only; no production function was
changed. The Rust source revision for this first gate is `b5406a591`; the final
callback-route guard is covered by the later gate below. Rebuilt in this job's
own host workspace using the retained cache, Solana 3.1.13/platform-tools
v1.52, locked offline dependencies, four jobs and the frozen feature sets.
Native RUSTFLAGS is `-C link-arg=-Wl,--threads=4`; the freeze recipe unsets it
only for SBF and uses `-C link-arg=--threads=4` as the target-specific flag.
Every build scope has MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0,
TasksMax=64. Reservation holds were respected. Time was expected in
incremental optimized compilation/linking, with no arithmetic gate.

| Program | SHA256 | Exit | Wall s | Peak RSS KiB | Swap |
|---|---|---:|---:|---:|---:|
| default | `dfc2a91ab24e1ec4f57debd8f124cb4f6a3c38ba2662b7318e2e4f3b4acdde34` | 0 | 41.233 | 648668 | 0 |
| devnet | `fb2fc048f6499a4775051d0267c76e8ca273b28f557bfd3b5fb65b2f687c8b78` | 0 | 3.713 | 204192 | 0 |
| pool | `121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548` | 0 | 34.048 | 645152 | 0 |

All three pass `cmp --silent` against the preceding continuation's frozen
artifacts. `frozen-elf-check.json` contains exact commands, sizes, source
hashes and resource receipts; `#print axioms` is N/A for these Rust builds.
The SBF diagnostics remain in the logs; byte identity is the claimed gate.
Runtime suites were not repeated for cfg-only additions. No keys, accounts,
wallets, deployments, peer worktrees or branches were changed; no push.

## Stage 5: exact ROM specialization and zero-fill obstruction

`mask_block_rom` and `source_block_rom` quantify over the actual
`R1Z.RomFiniteBin.Address bound → OracleAnswer` table and use its `lookup`.
The answer-carrier adapter is an explicit data parameter; no byte/digest
bijection or source carrier is smuggled into the result. Env J 8153 passes.

The actual `Tape K F` contains `AffCoordinate = (Fin 10 × Fin 1024) ⊕
(Fin 3 × Fin 1024 × Fin 4)`. Thus H1 has 1024 × 4 raw ideal coordinates,
even though `state_only_hiding.rs` samples H1 only when the row is inactive
and not the dependent row. The raw dependent coordinate is subsequently
ignored by the model's `balance 0`; all raw coordinates remain in the tape
carrier and in `R_commit_equal_fibres`'s quantifier.

New `ProverCommitFibreScope.zero_fill_not_equal_fibres`, checked against that
actual tape type, proves: if a decoder has any success and fixes raw H1
lane 1 / row 0 / limb 0 to zero on every success, then **no** common fibre
cardinality exists over all tapes. The tape with that coordinate equal to
one has an empty fibre, while the successful tape has a nonempty fibre.
The proof is symbolic; it never enumerates the tape or input carrier.
Env J **8156**: exit 0, 1.92 s, peak 3,511,324 KiB, zero swap, standard axioms.
Draft 8155 failed on decidability/membership elaboration and is rejected.

This rules out a direct adapter that zero-fills unused ideal coordinates.
It does **not** prove every possible completion impossible, nor that the
existing conditional privacy theorem is false. A completion must supply
those coordinates with the required exact fibre law and reconcile its
success/failure classification with the shipped sampler; alternatively a
new quotient-tape endpoint must transport the existing model proof. Neither
construction is supplied here. D92 callback equality alone supplies neither.
No zero-filled `tapeOf`, assumed cF, reserved-secret law, or source prover
instance is installed to paper over this obstruction.

The final audit after these source additions is env J **8157**: exit 0,
**1.89 s**, peak **4,028,480 KiB**, zero swap. Its fifteen full axiom lines
cover all fourteen new theorems and the unchanged protocol endpoint; all
are subsets of `[propext, Classical.choice, Quot.sound]`. Attempts 8152 and
8154 are earlier successful audits, superseded after identified source
additions, not unchanged full replays.

A final Kani guard checks that `HOST_HASH` through the actual function pointer
increments the shared table's call counter and creates exactly one cached
point for a repeated input. It passes; this detects an ignored pointer stub.
That proof-only addition is committed at `8517407c1`. All three ELFs were
rebuilt again from this final Rust revision and match the same pins and
retained frozen artifacts (`cmp`); see `frozen-elf-final-check.json`.
