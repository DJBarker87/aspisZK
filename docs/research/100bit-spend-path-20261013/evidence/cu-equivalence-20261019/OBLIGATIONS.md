# CU optimization equivalence — completion requirements

Goal: full equivalence proofs connecting the retained optimized verifier to the
reference used by the existing soundness/privacy results, with no new unproved
equivalence premise at the final transfer boundary. This is **in progress**.

Reference: origin/research f458169f705f25b04e1e29546c621e4665e0f64c.
Optimized production source: 39c2971dd16c95858a4cfd2c9ae35da052eacfa9,
unchanged throughout the current proof-only work.
Existing candidate declaration inventories remain authoritative inputs.

The observation relation must preserve acceptance/rejection, cryptographic
query input/answer order, public/proof/checkpoint bytes and settlement effects.
Internal diagnostic log erasure must be explicit. Equivalence compares logical
executions with sufficient resources; it does not equate failure under an
insufficient compute/heap cap. Resource bounds and source caller admission
remain obligations, not hidden hypotheses asserting the conclusion.

| Retained change | Required proof and source bridge | Status |
|---|---|---|
| 1 gamma table reuse | power table correctness, unchanged caller dataflow, preparation/tx1 extraction | open |
| 2 opt-in observer | observer state noninterference, diagnostic-log projection, caller feature binding | open |
| 3 S2 inactive groups | literal table correspondence, finite regrouping, source execution | all 1024 Nat-model classification cells, bounds, first-occurrence order and weighted regrouping checked; emitted machine helper/field/decoder binding open |
| 4 delayed base dots | modular equality, all u64 bounds, decoder/failure-order and loop execution | symbolic arithmetic checked; source bridge open |
| 5 canonical private dots | WideExact invariant, redundant-check elimination, outer count implies inner bound, reduction/output | open |
| 6 public decode reuse | checked same-byte decoder/selector correspondence, first_decoded and adapter execution | open |
| 7 geometry reuse | node/denominator agreement, caller range validity, execution | open |
| 10 fixed prefix | admitted q length, identical decoder accesses and failure behavior | exact query bound and complete source slot/base/batch/tail comparisons checked; complete old/new kernel compared on 608-byte inputs; full-width four-slot constructor/caller and std-library admission open |
| 12 rho residues | every-prefix modular invariant, four-term overflow bound, canonical finish, array/caller execution, heap admission | integer invariant, complete push/value execution and frame/overflow proofs checked; finish now consumes the extracted standard next body; initialization, outer callers and serialization composition open |
| 14 Libra factorization | all four weights equal for arbitrary canonical challenges including zero; field/source execution | division-free cut/tensor algebra and handwritten list-loop correspondence checked; concrete field/machine/source bridges open |
| composition | refreshed emitted caller bodies, byte/error/effect preservation across tx1/tx2 and adapter | open |
| soundness transfer | apply existing soundness results under their original premises to the actual optimized source model | open |
| privacy transfer | preserve modeled observation/game distributions under original premises; do not claim timing privacy | open |
| release evidence | focused files, consuming bridges, coherent final closure replay and axioms audit; exact source/tool/feature pins and receipts | open |

`CuSavingsResidues` proves the dot and rho integer identities symbolically,
including arbitrary-length rho prefixes. It does not yet establish equality
of an extracted Rust loop. The successful receipt is `residues-e/receipt.json`;
failed attempts are retained and are not release evidence.

`CuSavingsLibra` proves the four algebraic weights after the 28-element runs
are split at the actual tensor cuts, for every commutative semiring and all
challenge values (including zero). The exact twofold loop-to-cut correspondence
and concrete tower-operation bindings remain required. Receipt: `libra-a`.

`AspisR1CuRho.{Types,Funs}` is promoted bytes-unchanged from the push/value
emission; the original full emission is retained under tooling as a diagnostic.
`FunsExternal` supplies concrete map/handback definitions, not the generated
axiom template. `CuSavingsRhoScalar` identifies the newly emitted reducer with
the verified current one, proves checked scalar multiply/add success and binds
the actual bitmask flush predicate. Receipts: `rho-types-a`, `rho-externals-g`,
`rho-funs-pushvalue`, `rho-scalar-a`.

`CuSavingsRhoValue.value_success` proves the complete freshly extracted value
method on every valid Vec index. It performs the actual array map and all four
reads, returning exactly the canonical residues of arbitrary u64 input limbs.
The read-success premise in the intermediate lemma is discharged by the
exported theorem from the index bound. Receipt: `rho-value-c` (standard axioms
only, 1.604 seconds, 2,670,712 KiB peak RSS, no process/cgroup swap).

The full emission's finish path originally did not typecheck against the
ordinary Iterator runtime: mutable iteration supplies a triple including a
handback, whereas the ordinary interface expects a pair. A namespace-local
concrete mutable interface now carries that handback; the original generated
trait instance and finish declarations compile bytes-unchanged under it.
`CuSavingsMutableEnumerate.enumerate_control_eq` checks compatibility with
ordinary enumeration after erasing handback. This is model compatibility,
not a completed Rust standard-library source-admission argument.

The existing unified source manifest check is not a proof replay. The older
readonly-metadata runtime result is not a universal formal premise proof and
is pinned to the older ELF. Neither substitutes for an equivalence theorem.

`CuSavingsRhoPushStep.source_update_step` proves one actual emitted update-loop
iteration, including checked multiplication/addition, both array reads, array
write and the Vec mutable handback. Its premises are local bounds and the
iterator next result; the enclosing four-iteration induction must discharge
these and prove the update/frame invariant. Receipt: `rho-push-step-f`
(standard axioms only, 1.604 seconds, 2,664,852 KiB peak RSS, zero swap).

Next: close the full update-loop induction and flush-loop handback, then
compose them with the already checked every-prefix residue invariant and
canonical value theorem. The remaining candidates and final soundness/privacy
transfer/replay remain required; this checkpoint is not goal completion.

The full `CuSavingsRhoUpdateLoop.source_success` and
`CuSavingsRhoFlushLoop.source_success` now check, including mutable-iterator
handback. `CuSavingsRhoPush.source_success` composes them with the exact
source flush predicate and proves bounded reference residues for every limb,
with an exact replacement-row frame. Successful receipts: `rho-state-c`,
`rho-update-loop-c`, `rho-suffix-map-a`, `rho-flush-model-b`,
`rho-flush-loop-f`, `rho-flush-array-a`, `rho-push-a`. All print standard
axioms only, use no process/cgroup swap and peak below 2.8 GiB RSS.

The prior Next paragraph about update/flush induction is superseded by those
checked results. Next rho targets: initialization, finish mutable-enumerate
runtime binding, and the actual outer verifier/canonical serialization callers.
No full optimization-equivalence or soundness/privacy transfer claim is made.

`CuSavingsRhoFinish.source_success` now proves the complete emitted finish
method under that concrete mutable runtime. Given only matching output/raw
lengths, it returns `canonicalSlice self`, the componentwise canonical
reduction of every arbitrary u64 raw row, independently of the previous output
values. The proof includes checked counter increments, every source value
call, indexed overwrite, full loop induction and mutable handback composition.
The structural list lemmas are symbolic, with no concrete-size normalization.

Successful receipts: `rho-mutable-runtime-c`, `rho-finish-emission-b`,
`rho-mutable-enumerate-c`, `rho-suffix-overwrite-a`, `rho-finish-model-c`,
`rho-finish-next-b`, `rho-finish-loop-e`, `rho-finish-a`. All have only standard
Lean axioms, no process/cgroup swap, peak RSS below 2.8 GiB and wall time below
2 seconds. Failed local proof attempts remain archived and are not evidence
of a theorem. `emit-finish.py --check` verifies the generated declaration cuts.

Still open for rho: admission of the new mutable runtime to the pinned Rust
standard-library/Aeneas source boundary, new/allocation, actual outer query
loops/counter, and reference checkpoint/canonical serialization composition.
The finish theorem does not discharge these by assuming whole-verifier
equivalence. All other retained-candidate bridges and final transfers remain
required. Production Rust remains unchanged.

The selected mutable next source now has a byte-preserving concrete-type
extraction and a checked forward/write-observation comparison with the local
runtime. See `ITERATOR-SOURCE.md` for the exact structural specializations,
tool failures, successful receipts and trusted frontend boundary. It exposes
a backward-count difference rather than claiming false whole-state equality.
The comparison must still be consumed by a finish-context proof; the source
binding is therefore not yet marked complete. Successful additional targets:
`borrow-option-types-a`, `borrow-option-operations-a`, `iterator-types-a`,
`iterator-source-option-a`, `iterator-next-a`, `iterator-source-shape-e`,
`iterator-source-bridge-a`. All print standard axioms only with zero job swap.

The finish-context source interpretation and consuming theorem drafts are now
registered separately as NOT_COMPILED pending targets. See
`FINISH-CONTEXT-PENDING.md`. Initial SSH staging failed before any Lean job
launched, and retries after the user's request still found the host unreachable.
No theorem success or source-binding completion is inferred from these drafts.

With the NUC still unreachable, the independent S2 table/algebra obligations
were checked locally using cached mathlib 4.32 objects. No Aeneas objects or
dependencies were rebuilt. `CuSavingsGroups` proves finite-sum regrouping for
arbitrary semiring coefficients and challenges. `CuSavingsS2Tables` discharges
its table premise against all 1024 exact fixed S2 classification cells, and
`CuSavingsS2Order` proves mask distinctness and first-occurrence order. All
group indices and row bounds are included. The generator pins the current
Rust source files and uses small named block certificates, not native_decide.

Thirteen additional targets are now checked; COMPONENT-AUDIT covers 44
components and separately retains the five uncompiled finish-context drafts.
Successful local targets take 1.1–2.2 seconds, peak below 1.5 GiB RSS and use
zero process swap. Local jobs use Lean's 7000 MiB limit and a descendant RSS
monitor stopping at 7 GiB, with direct cached-import preflight. They are small
focused jobs under the ordinary-development-machine policy, not large builds.
See `S2-TABLES.md` for source/model scope and remaining machine bindings.

After connectivity returned, all five pending finish-context targets passed.
The actual emitted standard next body is consumed through the unchanged finish
loop; `CuSavingsRhoSourceFinish.source_success` returns canonicalSlice under
only the matching-length invariant and `.source_eq_model` equates the result
with the earlier checked model. No equality of discarded backward counters is
assumed. Receipts: `rho-source-runtime-b`, `rho-source-next-e`,
`rho-source-finish-emission-b`, `rho-source-finish-loop-b`, `rho-source-finish-b`.
All print standard axioms only with zero process/cgroup swap and peak below
2.6 GiB RSS. See FINISH-CONTEXT-PENDING.md for the resolved historical block.

`CuSavingsPowerLoop` proves emission-before-multiply, every table read, and the
final updated state. `CuSavingsLibraLoop` checks all literal 16-slot blocks and
the 28-term cuts. `CuSavingsLibraProgram` consumes both to equate handwritten
list-loop models of all four weights for arbitrary semiring challenges,
including zero. These are not Aeneas machine-source equivalence claims.
Receipts: `power-loop-a`, `libra-loop-a`, `libra-program-b`; all use standard
axioms only and zero process swap. COMPONENT-AUDIT now covers 52 successful
targets and has no uncompiled targets; open obligations in the table remain.

The exact four-word initialization assignment is now separately extracted and
checked, including every widening cast, counter-zero residue bounds, canonical
round-trip and composition with source finish from a list initialization model.
Receipts: `rho-init-row-types-a`, `rho-init-row-funs-a`, `rho-init-row-proof-c`.
The full unchanged new method encounters an Aeneas borrow-analysis failure;
its zip/allocation source obligations remain open. See RHO-INITIALIZATION.md.

The fixed-prefix statement is now separately extracted and checked, including
its actual subslice/conversion/unwrap and short-input panic. All three decoder
range families remain byte-identical under the bound. COMPONENT-AUDIT covers
58 successful targets and now checks exact nonstandard axiom sets as well as
rejecting sorryAx. The prefix success/failure source theorems carry the
backend's opaque Formatter TYPE through Debug/unwrap; the byte/range/index
lemmas use standard Lean axioms only. See PREFIX.md for the exact boundary
and still-open View.query/four-dot source composition.

The complete View.query accessor now discharges the prefix bound from actual
source success. CuSavingsQueryPrefix composes it with the checked prefix and
all three exact decoder range families, preserving failure/divergence of the
query operation. The complete four-dot loop/array/closure comparison remains
open, so candidate 10 is not marked fully closed. See PREFIX.md and
AENEAS-NO-BRANCH-JOIN.md for exact source and frontend boundaries. The audit
checks these new source/emission pins and successful receipts, including the
Formatter TYPE in the composed query/prefix theorem. No production source,
protocol, fixture, checkpoint format or cryptographic call schedule changed.

The complete emitted old/new dot kernels now typecheck under universal shared
arithmetic parameters and a concrete state-threading array builder. Their full
same-608-byte comparison checks, and CuSavingsDotsSlotPrefix proves complete
actual slot execution is prefix-insensitive on arbitrary longer queries for
slot < 4, including all loops, checked operations and decoder failures. See
DOTS-SOURCE.md. The four-slot builder must still establish this index bound
and stable capture invariant, then consume the actual View.query bound.
Its standard-library source admission and concrete shared-helper interpretation
remain explicit; no optimization is newly marked fully closed. All new
successful receipts/axiom sets are registered in COMPONENT-AUDIT. Stopped
search attempts and symbolic replacements are in PROOF-SEARCH-REVIEW.md.
