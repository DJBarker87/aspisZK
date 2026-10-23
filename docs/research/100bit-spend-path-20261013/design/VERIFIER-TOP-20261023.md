# Verifier stage-entry assessment — 23 October 2026

Status: unchanged stage bodies extract successfully; S2 remains open. Branch
`codex/cx-verifier-top-20261023`. Receipts are at repository-root
`evidence/verifier-top-20261023/`.

## Frozen scope and intended claim

Assess actual `candidate::tx1`, `candidate::tx2_authenticated` and its
`tx2_common` continuation with cone top functions opaque. Successful extraction
is a prerequisite to source identity and the ordered cone decomposition;
no assumed callback identity will be reported as discharge.

The adapter theorem and the C5 checkpoint writer/resume endpoints are reused
only within their stated premises. No existing Lean module or shipped Rust
source is changed. Release pins and initial source hashes are in `target.json`.

## Validation and remaining obligations

Initial inspection only: zero Lean attempts, zero Kani runs, no new theorem,
no axioms audit, no release build. Target not yet established. Next deliverable:
an admitted capped extraction probe and its exact source/tool receipt, or a
minimal stage-glue restructuring proposal if the probe exposes an obstruction.

## Stage 1: actual stage glue extracts

Charon 0.1.223, built MIR, Aeneas preset, native Linux, release default
private-leaf-salts feature: roots are the exact current `tx1`, `tx2_common`,
`tx2_authenticated`. All other crate and protocol bodies are opaque; reached
value layouts are transparent. No Rust source rewrite, stub body, LLBC
transformation, or borrow-check bypass was used. Charon reports has_errors=false.
The first LLBC is 1,521,015 bytes, SHA-256
`1511b8380f4e5f39d58c23a5ef1d10d2406b951992ec8501e39e1c79e069dff6`.
Aeneas emits all three stage bodies, including every error branch and checked
slice/array operation. Raw output is retained as `.lean.txt`; generated external
axiom templates are *uninstalled tool output*, never accepted Lean premises.
The next extraction includes complete reached layouts to remove external type
holes, then parameterizes external functions as named operation fields.

| Attempt | Exact target | Exit | Wall s | Peak RSS KiB | Swaps |
|---|---|---:|---:|---:|---:|
| charon-001 | three actual candidate stage roots | 0 | 81.1184 | 539568 | 0 |
| aeneas-001 | VTop_Stages.llbc → Lean | 0 | 1.0329 | 128656 | 0 |

Both used admitted independent scopes: MemoryHigh=6G, MemoryMax=8G,
MemorySwapMax=0, TasksMax=64. Full commands, environment, source revision,
source hashes, limits and logs are in the respective receipt directories.
`host-overlay.json` pins 540 overlaid Rust/Cargo inputs; all hashes checked on
host before extraction. `toolchain.txt` pins both translator binaries and rustc.
No Lean theorem or op10/op11 installation is established by extraction alone.

## Stage 2: installed source identities and ordered accepted calls

`VTop_Types` shares already extracted Rust value layouts with AdapterRw and
AspisR1Stage2. This is a namespace/carrier adapter, not a new representation
or a cone proof. `VTop_Model` preserves the generated stage bodies and takes
24 generated external operations plus one pure std array-unwrap operation as
explicit `Ops` fields. No generated template axiom is installed. The unwrap
boundary is necessary because the backend's direct `DebugTryFromSliceError`
instance pulls `core.fmt.Formatter` into the axiom set (lean-003, excluded).
The accepted model (lean-004) uses standard axioms only. This boundary remains
part of the existing std/extraction interpretation, not a proved concrete std
instance. Remaining opaque nested public-layout templates are likewise not
installed; their already extracted complete carriers are shared explicitly.

`VTop_Entry.install adapter stage` sets only adapter op10 and op11 to the exact
extracted tx1/tx2_authenticated definitions. `op10_source` and `op11_source`
prove their identities for this installed dictionary, at every hash type and
digest dictionary. They do **not** assert equality of an arbitrary pre-existing
`AdapterRw.Ops` dictionary with this instance. `first_accepted` inverts the
actual adapter error map: its successful checkpoint is the same successful
stage return, with unit hash and observer None. Source span/hash checks in
`source-identities.json` identify all three extracted bodies with this
worktree's `candidate.rs`; they do not establish SBF lowering.

`VTop_Flow` lifts these exact bodies into typed operation syntax.
`VTop_Erasure.{tx1,tx2_common,tx2_authenticated}_source` and `_erasure` prove
full Result equality, including failure/divergence and inner Rust errors.
`VTop_Trace.Call` retains each operation's actual typed arguments;
`Event.returned` retains its actual return. `accepted_execution` derives an
execution trace from source acceptance, rather than assuming successful cuts.
`VTop_Order.accepted_tx1` / `accepted_tx2` derive those same-value traces and
the exact operation schedules below. They are not independent successful
executions selected to fill desired inputs.

- TX1: split guard → shape → canonical scan → Parsed mark → zero scratch →
  preparation (returned scratch included) → initial accumulator → Prepare mark
  → folded-root range/conversion → batch 0 → Merkle mark → geometry → pending
  weights → query loop → weight flush/back-write → checkpoint → write mark.
- Authenticated TX2: shape → Parsed mark → resume → split check → powers →
  read mark → inactive range/decode → folded-root range/conversion → batch 1
  → Merkle mark → geometry → pending weights → query loop → weight flush →
  relation-view construction → finish_relation.

All checked slice calls and pure array materializations remain in the tree.
`VTop_Cuts.writer_reached` and `resume_reached` independently invert acceptance
to the exact writer/resume child invocation on the original proof/public/CP
arguments. They supply no assumed checkpoint encoding or returned state.

The combined TX2-order proof hit the fixed 200,000-heartbeat limit in
lean-023 and, after a first smaller split, lean-030. Neither was rerun
unchanged. `VTop_SecondFlow` factors only the *Lean proof definition* at the
query-return continuation; `common_source` proves definitional equality with
the original monadic body. `VTop_SecondOrder` checks the four-operation tail
and the prefix separately (lean-032); the authenticated wrapper then composes
them (lean-033). No Rust/LLBC rewrite, cap or heartbeat increase occurred.

**Task (2) is partial:** source identities and accepted typed call order are
proved. The complete `OraclePortFrozen2Join.AcceptedRunJoin` observation is
not proved. An operation-return log is not a digest-query log. No theorem here
claims equality to `verifier D dV_frozen2`, equality of its two enriched
annotation passes, or inhabitants of the thirteen `PerConeJoins` fields.
