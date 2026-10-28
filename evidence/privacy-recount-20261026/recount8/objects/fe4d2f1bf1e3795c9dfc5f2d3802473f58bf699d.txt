# Runjoin44 — current opening arithmetic and coefficient permutation

Worktree `/Users/dominic/ZK/.worktrees/pv-runjoin`, branch
`codex/pv-runjoin-20261026`. Entry `440982374b8b76df08cce274eed75f3637773fce`,
resume LOG D404. Source revision at final validation `57ea839aa8a47efc02b35fdeb8586bb0ace88515`.
Assigned IDs **60700–60799**, audit IDs **60797–60799**.

**Target not yet established. Whole ledger rows removed: 0.**
Stopped on the **100-attempt Lean budget**: **62 accepted / 38 rejected**,
**0 Kani**. Every assigned ID had exactly one compiler launch. All three
reserved audits passed. The unlaunched staging rejection and admission refusal
are separately recorded and uncharged.

## Accepted source/model results in step (2)

`PV_RunJoin_GammaAssociation44.complete` associates the current complete
`prover.opening_batch` Result with `ProverCommitGammaOutput53.run`, on arbitrary
canonical coefficient cells. The proof covers all 29 stored lanes and all 1024
rows, with exact vector order and fixed-array image. Its dictionary explicitly
installs the retained source powers function. This installation is a source
construction, **not a native callback or runtime-effect association**.

`PrimalFirst44.complete`, `PrimalSecond44.complete` and `DualFirst44.complete`
associate the actual current primal 1024→256, primal 256→64 and dual 1024→256
folds with the retained complete producers. They prove ordered vector contents,
canonicality and scalar/model values. Four child indices, source bounds, checked
division, wrapping counters, raw wide add/multiply and quarter scaling are proved
symbolically. No successful fold or desired byte equality is a premise.

`RoundAssociation44.complete` associates the complete current round with the
retained quarter-scaled round producer; `RoundSecond44.complete` handles the
256-cell second round and its exact live-prefix padding. The proofs retain the
source permutation, d/s/t order, coefficient updates, both input lengths and all
seven scales, without reducing a concrete 4096-transition recurrence.

`OpeningKernel44.complete` composes these **actual source arithmetic calls** in
producer order with `ProverCommitOpeningKernel49.run`. `OpeningEncoded44.complete`
then proves all three complete actual encoders and their ordered retained byte
streams: seven c0 values, seven c1 values and 64 final values. This is an
arithmetic/encoding kernel result. Its `run` definition does not contain the
constructor's intervening transcript, commitment, tree or weight-state calls;
it is **not** the whole `PreparedOpening` association.

`CoefficientRow44.row` proves the complete retained source
`ProverRwSuccessCoefficientsSource.transport.Variant.row` Result, using all five
checked digit transitions, the iterator's returned state, checked usize products,
checked shifts and exact u32 shift-count casts. `CoefficientRowMath44.value`
identifies its machine-bit permutation with `AspisR1.rowNat`.
`CoefficientArray44.complete` proves the complete ordered 1024-entry source
coefficient-array Result for arbitrary element type, input values and Copy
dictionary. It uses the retained ordered FnMut/fromFn model; native standard
library adequacy remains separate.

Five required inherited machine/base-four permutation modules were resolved by
EJR/freeze/h5 precedence, source-hash checked and compiled once in topological
order, IDs 60764–60768. `coefficient-row-resolution.json`,
`coefficient-row-staging.json` and `coefficient-row-order.json` record provenance.
No unchanged accepted object was rebuilt. Two accepted inspection modules print
the actual checked-shift/iterator definitions; they supply no standalone proof
or native credit.

## Retained gap and rejected candidates

**Step (2) remains incomplete.** The current `prepare_opening`/`finish_opening`
constructors are not yet associated with `ProverCommitOpeningModel53.exact_result`.
The actual weight constructor/raw/materialization state, coefficient Vec assembly,
claim evaluation, intervening transcript challenges and folded-domain/tree calls
still need their complete caller associations. The 22-query append, six node
multiproofs/publication indices, and complete ordered `publish_compact` proof
bytes remain open. Neither append helper is credited here from the smaller
encoder results.

Attempt 60795 (`CoefficientsVector44`) reached default recursion/heartbeat limits
at selected-dictionary conversion and vector aggregation. Attempt 60796 isolated
the selected op255 association (`CoefficientInstalled44`) and still hit the
unchanged default recursion limit. These are rejected candidates, not checked
counterexamples. `CoefficientsCaller44` is an uncompiled dependent draft.
`new-source-credit-status.json` names all three uncredited current sources;
`not-compiled-staged-modules.json` names the two staged ones. Failed sources are
retained as verified Git blobs in `retained-failed-sources.json`. No limits were
raised and no rejected source was recompiled unchanged. The retained generators
were updated to preserve the accepted symbolic proof forms;
`generator-output-identity.json` checks nine generated targets against their
accepted current sources byte for byte, without writing or recompiling Lean.

Steps (3) and (4) were **not started**, respecting the requested order. Both native
ROMView decoder laws supplied to CommonSample32/CommonObserver32, installed native
helper effects, the security-model proof-byte equation and RustRealRefinement
remain open. OracleBridge38's selected-callback theorem retains its single named
op227 hypothesis unchanged, and is not used for credited endpoint removal.
**Op227 is not the sole remaining refinement gap.**

## Endpoint and deployment boundaries

Removed/added/weakened/changed endpoint premises: **0/0/0/0**.
V038, V045, V163, V165, V167 and V244 remain. Before and after, the eight
PV_RunJoin_Premises fields are exactly source_V045, E1_V329, native_fill_V336,
native_ledger_V337, byte_blind_V338, kernels_V339, disclosed_V038 and
observerOracle_V038. TrustItems remains exactly entropy_law, entropy_kernel,
observation. `endpoint-boundaries-unchanged.json` checks byte-identical source
statements, including both Common interfaces, trust and ledger files.

The observer/simulator, coupling, bad/query events, failure and divergence
observations, public guards, failure-independence and side-channel obligations
are unchanged. Compiler-cohort, deployed features/profile/ABI, D188, native
allocation/TLS/filesystem, Drop/unwind, K-1/K-2 and all other prior qualifications
retain their scope. No new native or deployed-code credit is claimed.
`stage-A-source-identity.json` verifies the empty frozen Rust/client diff from
82566acdfb. Historical artifact evidence is reused only in that source-identical
scope. No shipped file, other worktree, shared source/cache, key/account or
release artifact was modified. No extraction, Kani/native differential, ELF
rebuild, push, merge or unchanged full regression was run.

## Validation and receipts

Initial read-only preflight: 2702 project source/object pairs, 5681 direct import
fingerprints, 5673 external objects and 5438 IR companions. Final preflight:
**2764 project pairs**, **5802 import fingerprints**, **5673 external objects**
and **5438 IR companions**, all matching. Both full preflights are compressed
with uncompressed SHA-256 sidecars. The pinned private runjoin32-lean cache is
retained; this is not a frozen-manifest release replay or an endpoint-closure
replay.

Every compiler ran as one module in one scope, MemoryHigh=6G, MemoryMax=8G,
MemorySwapMax=0, TasksMax=64 and Lean -M7000. Every admitted launch had allowed:true
and admission exit 0. One reservation refusal was uncharged; its full cooldown
preceded further admission and ID 60785 was retained. Own staging/commit-input
corrections are recorded in `local-input-corrections.json` and
`unlaunched-input-60717.json`; no host infrastructure was repaired or changed.
Scope intervals are disjoint in `scope-sequence-check.json`.

| ID | Focused audit | Exit | Scope wall s | Peak RSS bytes | Swap |
| --- | --- | --- | --- | --- | --- |
| 60797 | R1Z.PV_RunJoin_OpeningAudit44 | 0 | 2.13 | 4417273856 | 0 |
| 60798 | R1Z.PV_RunJoin_CoefficientAudit44 | 0 | 2.02 | 4398473216 | 0 |
| 60799 | R1Z.PV_RunJoin_SourceAudit44 | 0 | 2.08 | 4442931200 | 0 |

All accepted printed axiom sets are subsets of propext, Classical.choice and
Quot.sound. `receipt-*.json` and `modules-*.json` record exact targets, commands,
source revisions/blobs/hashes, dependency fingerprints, exits, wall times, RSS,
swap and printed axioms. `original-module-logs.json.xz` hash-verifies all **100**
original output/time pairs. Peak RSS was **4452421632 bytes**; every swap count
was zero. There was no memory kill or external timeout. Toolchain and zero own
running scopes are recorded in `toolchain-and-final-scopes.json` (Lean 4.32.0,
pinned commit 8c9756b28d64dab099da31a4c09229a9e6a2ef35).

## Next concrete deliverable

Replace deep definitional reduction of the selected op255 dictionary with named
preservation/association lemmas, then finish the actual 29-column
`opening_coefficients` Vec assembly. Bind the current stored weight state and
materialization and both actual opening constructors to
`ProverCommitOpeningModel53.exact_result`, retaining all transcript and Result
branches. Only after that constructor association is complete, finish the actual
query/node append byte lists and `publish_compact`, followed by steps (3) and (4).

`commits.txt` lists commits since entry; the final evidence-freeze commit follows
its generation. No privacy target or whole ledger row is claimed established.
