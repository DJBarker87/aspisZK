# R0 SEM draft — compile record

2026-10-07. Statement/design work only; no theorem was proved and no open
premise was supplied as an instance. Read AGENTS.md and the sources listed in
SEM_SPEC.md. Fetch/fast-forward found branch `research/v8-wide-reference-20261005`
at inspection revision `c4ca596c83e29e858e0ee88887ccf9f9ea987f5a`.
The final design and Lean source are committed at
`e3bc4fc465f2700ec62376ce20158437404a421d`; concurrent commits elsewhere on
the shared branch do not change that source pin. Only this new directory was edited.

## Environment and invocation

Host `dombarker@100.108.41.90`, Linux 6.8.0-142-generic; Lean 4.32.0,
commit `8c9756b28d64dab099da31a4c09229a9e6a2ef35`.
Let T=`/home/dombarker/project-offloads/aspis-fs-generic-20261006` and
B=`/home/dombarker/project-offloads/ZK-v7-one-tx-formal-consolidation-20260828/AspisFormal`.
Created real directories T/sources/R0S and T/objects2/R0S; reused the pinned
FS/FS2/R0FS/R0/Wide/V8 object mirror. No dependency or package rebuild.

Command: `T/run2.sh 602 R0S/SemStatement 7000 7`.
The runner uses the captured `lake env` environment in
T/evidence/environment-base.json, invokes `lean -j1 -M7000 -DElab.async=false`,
and writes T/objects2/R0S/SemStatement.olean. The scope has MemoryHigh=5G,
MemoryMax=7G, MemorySwapMax=0, TasksMax=128 and a 900-second timeout.
The final reservation check admitted 30 GiB populated + 7 GiB under its 55 GiB
ceiling. One task Lean job at a time; no cap was raised.

LEAN_PATH, in order: T/objects2; then
B/.lake/packages/{Cli,batteries,Qq,aesop,proofwidgets,importGraph,LeanSearchClient,plausible,mathlib}/.lake/build/lib/lean
(each brace member is a separate colon-delimited entry); then
B/.lake/build/lib/lean; then
/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean.

## Focused attempts

All rows target `R0S/SemStatement`. Times/RSS are `/usr/bin/time -v` around
the captured-environment Lean invocation; exit is the Lean scope's status,
not the outer runner's exit. Raw records are T/evidence/out-N.log,
time-N.log and sha-N.txt. No unchanged failing job was rerun.

| Attempt | Source SHA-256 | Exit | Wall s | Peak RSS KiB | Swaps | Audit |
|---|---|---:|---:|---:|---:|---|
| 600 | 807ed94f94974c4875d7cffb3d2d7ec40577db7a22d544ec0259adcbeaba4e84 | 1 | 3.46 | 6765504 | 0 | failed elaboration; not evidence |
| 601 | 5f68ba27f6f2fea04309327cbe45fe41d2361e3e39fa8833b25591b1567e790b | 0 | 3.55 | 6803420 | 0 | standard axioms only |
| 602 | 21423173ee567da77beac5837fffc50c8c891b11818086e06b5b20c35eda1a38 | 0 | 3.90 | 6802852 | 0 | standard axioms only; final committed source |

600 failed: unresolved InitialMessage/InitialWord namespace, wrong dot namespace,
and missing parentheses around a product binder; fixed before 601. No failed
object was consumed. The final replay 602 records the committed source after
clarifying the C1-before-lambda/chi comment; no further Lean replay was needed.

`#print axioms`: roundPolynomial, terminal, Algebraic, RelationExtractionTarget,
SEMTarget, SEMImplicationTarget, D2Target, CoverageTarget and proposedEpsilonSEM
use only `[propext, Classical.choice, Quot.sound]`; toOpeningData uses
`[propext, Quot.sound]`. These are definition-dependency audits, not soundness
proofs. The final file has no theorem/lemma declaration, proof block, forbidden
placeholder, custom axiom or resource-option override. Probability/counting
uses abstract finite types; no concrete State/Addr/WideExact univ is unified.

The note's 38 reference targets exist; `git diff --check` passed. The budget
calculation used exact p^4-1 and 45-digit Python Decimal logarithms:
397030 gives 105.401111499850264282550195499990532119874282 bits;
396430 gives 105.403293379691776602676937402552113104923687 bits.
These numbers are proposed ledgers, not verified SEM bounds. The inactive
count 810 is literal mask-array inspection, not a new Lean proof.

## Main source provenance

All contents below were inspected at the inspection revision above. Paths
are relative to the repository; last-change commits and content hashes make
the retained baseline/source choice reviewable. Other references in SEM_SPEC.md
are also pinned by the inspection revision, not by a moving branch.

| Path | Last change at inspection revision | SHA-256 |
|---|---|---|
| `docs/research/v8-no-work-100-20260907/baseline.md` | `6195feca2dbfcfa8df51b83331582c4779218dd9` | `044a467621479439764e415e44c1e8c45bf389743d30bfb1a5b6920ae22729f8` |
| `docs/research/v8-no-work-100-20260907/experiments/performance_verifier.rs` | `d3963b99c580bc5b906b1fb03e681d0a226017d5` | `bf8a24c42c0d5493d2259fa19a70b1a8bf4ba168f661b71cfed6d33c70eebfbc` |
| `docs/research/v8-no-work-100-20260907/experiments/payment_extraction.rs` | `d3963b99c580bc5b906b1fb03e681d0a226017d5` | `a8c18d8999623a71fe97da9b85dd7f010dc3c5bc23d44943fc5bcb123881ac82` |
| `docs/research/v8-no-work-100-20260907/experiments/positive_transfer.rs` | `d3963b99c580bc5b906b1fb03e681d0a226017d5` | `f5031b80ff2d9f40689f2bd6d18323be330664bedd0aec24b34bd67aeeea12a8` |
| `docs/research/v8-no-work-100-20260907/experiments/recovered_witness.rs` | `1e801655557ab06499d821af2218cbca7351c4aa` | `56760c46ed56ace2756949efabc09f1a2b8880087c1b4dbb7da394a1cc54132f` |
| `docs/research/v8-positive-complete-devnet-20260909/upstream/performance_verifier.rs` | `4a12e34f5bdbe59b63f23d8ddba154845d86a997` | `bf8a24c42c0d5493d2259fa19a70b1a8bf4ba168f661b71cfed6d33c70eebfbc` |
| `crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs` | `61e6dfc245d3c1d867b7424519e2be608bd26aac` | `efbc5be87e271419d7b09e1bb6e3a83984d42795bc20067ea039814fb89ffa58` |
| `crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal_constants.rs` | `b5c88c3ec6dd1c418d51813a793b46d4a189f7c5` | `cfce7ec499d3cfd54cf91eb88675e45d89ada5ce073fe00c78be5211204fbc50` |
| `crates/aspis-core/src/state_only_hiding.rs` | `cfee66131d7f296af77cf86d0e09f7371265dce2` | `18058112db3108a18f9d11f8d9ffb6f9c1b310b90b333010fd0f98cac480237f` |
| `AspisFormal/AspisFormal/Pool/V7K15FailureRootInventory.lean` | `6e3df7bd54fb55db0a74ecdcad4c4e3217c7774f` | `18cddfa3de053e3b9faae6f7c3d3ae0addeb392f26e5b50b6128e15d11de170e` |
| `docs/research/v8-wide-reference-20261005/lean/R0/OpeningDefinitions.lean` | `fafadada7f23b7b223643ca1e84d2fa068866066` | `6368b282b28ff076b54dae55fd53556c8f09c5cae8710ac9e4782c64ef57138a` |

Lead decisions and proof-route estimates are in SEM_SPEC.md §D and §C.
No proof job should infer answers to those questions from this compile.
