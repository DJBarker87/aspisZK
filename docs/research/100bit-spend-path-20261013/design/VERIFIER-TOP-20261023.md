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
