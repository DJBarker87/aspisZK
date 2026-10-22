# Part 52: terminal dependency closure and simulator continuation

**Target not yet established.** Branch `codex/cx-prover-commit52-20261022`.
Only J10400–J10499 are authorized for proof attempts. Cold dependency work uses
separate BUILD-52 labels. No shipped crate or program source is changed.

## Stage 1: cold dependency preflight

BUILD-52-1 ran the pinned terminal-cone preflight in a dedicated host scope:
MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64. The populated host
reservation before launch was 26172456960 bytes plus this scope's 8 GiB.
The scope exited before any Lean invocation: Env J lacks both objects and
staged sources for eleven external imports. The first unresolved module is
`AspisR1SelectedMaskProbe.Funs`. Exact console and GNU-time output are retained
under `evidence/prover-commit52-20261022/build/` in the 100bit-spend-path tree.
Exit 1; wall 0.07 s; peak RSS 31184 KiB; swaps 0; source revision
`223a37671e784ddeeab6bd8295df24fdb2647a79`; axioms audit not applicable (no Lean
compile and no new theorem).

Read-only source resolution expanded the preflight to retained extraction
evidence and the retained Lean 4.32 arithmetic port. The resolver accepts
additional repository copies only when all candidate bodies have the same
SHA-256; its decisions are in `build/resolution.json`. The two missing
SelectedMask field modules use the audited arithmetic port's unchanged
`sources/` files, with original paths and hashes in `build/plan.json`.

The expanded preflight succeeds and schedules **529 missing modules**. The
single compiler pass is BUILD-52-2 (BUILD-52-1 invoked no compiler). It runs
sequentially in one scope with the same limits, asserts the actual cgroup
settings, monitors aggregate child RSS, stops near 7.5 GiB RSS or after ten
minutes without a new target, and stops at the first compiler failure. Existing
objects are reused and never overwritten. No Session A source is edited.
The J10400–J10499 launcher preserves the existing no-unchanged-rerun guard.

## Cold compiler result and isolated obstruction

**BUILD-52-2 failed at module 262 after 261 successful module builds.**
Exact targets are the three roots in `build/plan.json`. Source revision:
`223a37671e784ddeeab6bd8295df24fdb2647a79`. Exit 1; total GNU-time wall
490.65 s (driver module-pass wall 490.5145 s); peak GNU-time RSS 4170212 KiB;
maximum sampled aggregate RSS 4294701056 bytes; swaps 0. The cgroup memory
peak is 675958784 bytes, a distinct charged-memory metric rather than RSS.
All memory high/max/OOM/kill event counts are zero. The scope is inactive.

`build/modules-audited.json` records every attempted module's source SHA,
dependency fingerprint, exact compiler command, exit, wall, GNU-time peak RSS,
sampled aggregate RSS, swaps, source revision and complete printed axiom reports.
All **552 printed axiom reports** in the cold pass use only subsets of
`[propext, Classical.choice, Quot.sound]`; full outputs are also preserved in
the per-module logs. Modules without a printed report are not described as
freshly audited declarations. No new theorem is introduced by the cold build.
`build/built-objects.json` records SHA-256 and size for the 261 new shared-cache
objects; no binary is committed. No prior shared object is overwritten.

The failing module is `ExtractedDecoderCallerBridge`, source SHA
`d7b5678e7626bcdfa93b630018b594332a484cbb92dc54151519bd9ca141c29d`,
label `BUILD-52-2-262`: exit 1, wall 0.7525 s, peak RSS 1855512 KiB,
zero swaps. Its verbatim error is:

```text
error: import AspisR1TerminalDecoder.Types failed, environment already contains 'instDiscriminantPoolV1TransitionKindU8' from AspisR1WithdrawalCaller.Types
```

Both owners compiled individually in this same pass: caller Types at 254 and
decoder Types at 257. The generated `@[discriminant u8 [1,2]]` attributes on
their distinct namespaced `pool_v1.historical_anchor.PoolV1TransitionKind`
types create the same unqualified instance name. This is an import-union
collision, not pathological reduction or a memory failure. The exact source
spans, hashes, complete compiler error and dependency path to
`CompositionPartsAfterValidationExact` are in `build/obstruction.json`.

The pass stops at this failure. There is no compiler rerun, no cap increase,
and no Session A edit. The task explicitly permits building Session A's
modules but prohibits editing them. The concrete next owner repair is to give
the generated discriminant instances type-qualified names while preserving
their readers and constructor tags, then rebuild the affected import union
and dependents. This repair has not been performed here.

The read-only post-failure inventory (`build/remaining-closure.json`) finds
121 missing objects in the composition root, including the failed bridge;
144 in the separate Poseidon candidate root; and three in the independent
arithmetic root. Finishing the Poseidon cone one module per proof attempt
exceeds the entire 100-number allocation. No second cold compiler pass or
broader manifest replay is launched.

## Independent arithmetic continuation

The independent retained equality-product/loop and terminal arithmetic suffix
pass separately under J10400–J10402. They do not import the colliding
decoder/caller union. These are unchanged retained proofs, not discharge of
their upstream composition input. Exact receipts follow in `build/J104*.json`.
All three use MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64,
Lean `-M7000`, and the same source revision recorded above. Every printed
axiom report is exactly `[propext, Classical.choice, Quot.sound]`.

| Attempt | Exact module | Exit | Wall (s) | Peak RSS (KiB) | Swaps |
|---|---|---:|---:|---:|---:|
| J10400 | EqualityValueProduct | 0 | 1.58 | 3964372 | 0 |
| J10401 | EqualityValueLoop | 0 | 2.18 | 3989976 | 0 |
| J10402 | TerminalPartsArithmeticExact | 0 | 1.70 | 3972380 | 0 |

J10403–J10499 remain unused. No complete manifest is replayed after the cold
failure; unchanged adversarial/runtime/ELF suites are not rerun. No file under
`crates/` or `programs/` changes, so the shipped-file rebuild rule is not
triggered. No ELF byte-identity rerun is claimed. No wallet or key is touched.

The helper initially tried executing the non-executable launcher directly;
the OS rejected it before any compiler invocation. Invoking the existing
launcher with `sh` fixes that tooling issue; no Lean input is retried.

## Contract inspection and remaining interfaces

Read-only inspection identifies `PoseidonLeadingPairExact.source_success`
and `PoseidonInterpolatedFullPairExact.qm_source_success` as potential inputs
to the candidate callable contract. Their additional import closure is not
compiled. Two missing original Session A source files are retained byte-for-byte
under `retained-sources/`, with origin paths and SHA-256 pins; they are evidence
recovery only and are not new accepted theorem results.

The retained projected wrapper pins extraction-candidate Rust SHA
`82d54bbade8d81899c64ede23befce8b240b881d61b144e769c0d0e16ab5cff9`;
the current frozen `crates/aspis-statement/src/state_only_poseidon.rs` has SHA
`4467d15c9d473cbd42caf33f21aa0192bed007b58ccaa4a61cb5691532cab7fe`.
Those whole-file hashes alone neither establish nor refute the required
function-level correspondence. No candidate theorem is promoted to a native
source contract without that binding.

No source Poseidon contract, complete interface 3 integration, or interface
4–6 closure is claimed. Remaining: complete semantic oracle/terminal producer,
guards and original-round assembly; complete Weights/gamma batching; source
opening helper/caller composition; and native simulator output equal to the
`R0Z.RefPayload.simE` payload. The deployed `RustProverRefinement` premise,
quantifiers, failure events and bound remain unchanged. No FSExperiments
conversion or joins are attempted. **Target not yet established.**

## Endpoint before/after

The verbatim before endpoint is preserved in this part's `endpoint/before.lean.txt`.
The deployed refinement remains explicit. No interface closure is claimed yet.
