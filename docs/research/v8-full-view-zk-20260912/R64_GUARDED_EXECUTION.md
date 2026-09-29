# R64: optimized M31 generated execution and inverse bridge

Base `a40fb23673ab80c67e99c06bf156f338b12b2a2e`, branch
`research/v8-r64-guarded-m31-20260929`. This completes the M31 execution
dependency left by R63 and the earlier R64 checkpoints. It does not complete
the extension-field, sampler or full-transcript privacy proof.

## Exact result

**Four focused leaves compile; 14 new execution theorems and nine retained
arithmetic theorems pass their axioms audits.**

- `GuardedFieldSlice.lean`: nine byte-identical declarations from a fresh
  extraction of the selected R62 field source. Imports/namespace framing are
  narrowed; no generated declaration is replaced by a handwritten algorithm.
- `GuardedM31Execution.lean`: six theorems prove the checked generated reducer
  and guarded multiply agree with R63's retained generated implementation.
  The multiplication equality holds for **every pair of U32 words**, including
  either noncanonical-input fallback. Its output is always the canonical
  product modulo P. The proof includes U64 multiplication/addition bounds,
  subtraction guards, the positive signed shift count, narrowing, and branch
  behavior. R64's previously compiled Nat bounds discharge the machine steps.
- `GuardedInverseExecution.lean`: eight theorems transport pointwise `Result`
  equality through the actual newly generated loop body, partial loop,
  square wrapper, inverse and extraction-only entry point. All-count square
  correctness is inherited from R63's induction. A canonical nonzero input
  succeeds with its canonical field inverse; zero returns `assertionFailure`.

The generated inverse equality itself is on all U32 inputs. The mathematical
field-inverse corollary correctly retains its canonical/nonzero preconditions.
No termination, inverse, masking or hiding premise was added. Axioms reports
contain only standard `propext`, `Classical.choice`, and/or `Quot.sound` (none
for the retained product-bound theorem); no `sorryAx` or new axiom occurs.

## Source audit caught and repaired the extraction profile

The NUC reconnected. Before restarting anything, the interrupted proof unit
was confirmed inactive with no output directory; the successful extraction
directory remained. Its artifacts were retrieved and audited.

That audit found the small extraction crate's **default release profile** had
produced wrapping arithmetic. The selected SBF execution explicitly uses
`CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS=true`. The earlier extraction is retained
as a rejected profile control, not reused as proof input and not represented
as a protocol defect.

The corrected recipe sets that same overflow environment variable and records
it. Charon/Aeneas were rerun once with this identified environment change.
All four field/include source files remained byte-identical. The new generated
declarations use checked operations, including the source's `31#i32` shift in
the optimized branch. The old retained reducer uses its `31#u32` shift; both
actual runtime semantics are accounted for, not textually conflated.

Pinned checked artifacts:

- LLBC: `4b0e277bf34236edc524a2731351be81d44d8070a57ff35570482e2376f0795d`.
- Funs: `6a391404ad5afbcaff3046f91d7885f531ac913ca60a4a60da9d8173148721a7`.
- Types: `49f7423d46c9a89c93e986cd74dd48ff51c0df00ac19c245f64386537eead35e`.

The extraction uses the retained pinned Charon/Aeneas binaries, Rust
`nightly-2026-06-01`, release/offline/locked/one-job compilation, and a
dependency-free wrapper calling the unchanged source's `M31::inv`. Translation
metadata contains seven local nonopaque functions, one type and one global;
there are no extra generated opaque function premises. Standard Aeneas runtime
operations remain part of the retained model.

The audit checks all 197 selected-stage pins before compilation, all 11
extraction pins, the four unchanged source files, nine exact declarations,
nine negative declaration mutations, and rejection of the wrapping-profile
artifact. Both extraction variants, including LLBC, source copies, generated
code, metadata and timed logs, are retained in the evidence.

## Compilation and resource record

Final focused `lake env lean -j1 -M4500` replay, one leaf at a time:

| Target | Exit | Wall | Peak RSS (KiB) | Axioms reports |
|---|---:|---:|---:|---:|
| CanonicalProduct (retained arithmetic) | 0 | 0.50s | 919,420 | 9 |
| GuardedFieldSlice | 0 | 1.24s | 2,504,888 | 0 |
| GuardedM31Execution | 0 | 1.28s | 2,512,516 | 6 |
| GuardedInverseExecution | 0 | 1.68s | 3,668,548 | 8 |

All swaps are zero. Checked extraction took 1.01s at 219,144 KiB peak RSS;
translation took 0.35s at 67,936 KiB. Both exited zero. NUC scope limits were
MemoryHigh=5G, MemoryMax=7G, MemorySwapMax=0, TasksMax=128, with at most 7 GiB
reserved simultaneously. No cold Lean dependency build or memory-cap increase.

The final cache reuses 299 targets and contains 303. There are 141 local/runtime
source and runtime-object dependency pins. Focused predecessor checks preceded
the bridge and one final four-leaf replay. Two multiplication-development
failures and one inverse-development failure are retained; they were tactic
rewrite/notation errors, not resource failures. The early draft runner carried
the R63 base label; the final release records the exact current base above.
A harmless tactic-style linter warning remains in the inverse leaf.

Final cache: `/home/dombarker/project-offloads/aspis-r64-final-20260929-a`.
Corrected extraction: `/home/dombarker/project-offloads/aspis-r64-extracted-20260929-b`.
Read-only local audit:

```
NO_DNA=1 python3 docs/research/v8-full-view-zk-20260912/tools/check_r64_execution.py
```

## Remaining proposition and full-goal boundary

**First remaining source proposition:** compose the actual CM31/QM31 norm,
negation, equality and `try_inv` operations with this M31 inverse, then the
circle map and bounded sampler/observer execution. R60's exact-field tower
theorems are available, but are not that word-level composition.

This result is under the pinned Aeneas extraction/runtime model. It is not a
verified Rust compiler theorem or a proof of SBF machine code, full panic/log
observations, the whole field tower, sampler or verifier. In particular,
`Result`-level failure equality here is not full-publication failure privacy.

The larger goal remains open: shared-oracle and seed/commitment laws, every
observer disclosure, causal transcript simulation, failures/retries/publication,
and justified numerical loss bounds. Coherent pre-beta quotient-pair extraction
remains a separate soundness obligation. C1 negatives, fixed-block hiding and
joint coverage retain their distinct status.

No protocol/runtime change, new SBF measurement, merge, deployment or wallet
operation occurred. Selected CU remains **1,497,377 / 1,498,764**; both actual
1M runs exhaust. This is source-proof progress, not a CU saving.
