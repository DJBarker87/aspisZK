# Part 51: native simulator continuation

**Target not yet established.** Branch `codex/cx-prover-commit51-20261022`.
Only J10300–J10399 are authorized. No shipped crate or program file is changed.

## Endpoint before/after

Verbatim endpoint snapshots are in `evidence/prover-commit51-20261022/endpoint/`
under `docs/research/100bit-spend-path-20261013/`. They are identical to part 50.
`RustProverRefinement` remains explicit, with unchanged quantifiers and bound.

## Stage 1: duplicate declaration ownership

`Linear50` imports `Batched48` and reuses its byte-identical CM31/QM31
`mul_m31` definitions. No Session A module is edited. The replacement binder
checks the extraction bodies against that single retained owner so regeneration
preserves the fix. The six affected targets are rebuilt in J10300–J10305;
the combined audit is J10306. Shared sources and objects are snapshotted in the
branch-named host workspace before replacement. All needed dependents are
rebuilt with new dependency fingerprints.

Exact targets, source revisions/hashes, dependency fingerprints, exit status,
wall time, peak RSS, swap and full printed axioms are recorded in
`lean/attempts.json` and `lean/receipts/` in that evidence directory.
All jobs use MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64;
Lean retains the 7000 MiB internal limit. No cap increase is used.

## Stage 2: symbolic caller split

The old J10298 failed at `ProverCommitMaskArithmetic50.caller` with kernel
excessive memory consumption: exit 1, 19.10 s, 7170376 KiB, zero swaps.
The replacement first proves `ProverCommitBind51.three` over an arbitrary
carrier and arbitrary Result-valued callees. Concrete source conversion,
array construction, and all three callees are locally opaque at the composition
boundary. No large computation is reduced; the existing individual arithmetic
proofs are reused. `ProverCommitMaskArithmetic51.caller` keeps the exact old
coefficient-law premise, input quantifiers and conclusion. It passes J10311:
exit 0, 1.82 s, 4046236 KiB, zero swaps, standard axioms only.
J10307/08 are rejected symbolic let-normalization drafts; J10310 proves the
corrected helper. J10309 is retired before compilation (missing dependency
object). The coefficient producer remains the next obligation; this conditional
caller is not complete native selected-mask success.

## Stage 3a: complete selected-mask coefficient producer

J10317 proves the owned 26-write loop's canonical output and symbolic overwrite
sequence. J10316 proves the exact source destination schedule is injective,
bounded by 27, and omits 23. J10320 proves the generic overwrite invariant and
finite monomial coefficient laws; J10324 splits the combined schedule into the
16 c1 and 10 mask-only summands. No Boolean cube or large concrete term is
normalized. J10326 proves `ProverCommitMaskProducer51.exact_result`: actual
owned array production succeeds and every decoded output cell equals its
selected-mask polynomial coefficient. The old coefficient-image premise is
discharged in J10327 `ProverCommitMaskCaller51.exact_result`, composing producer,
linear forms, prepared Horner and final arithmetic. Canonical input values and
the explicit B.i/B.u basis representation equations remain; complete semantic
oracle provenance is still next. J10327: exit 0, 1.66 s, 4048744 KiB, zero
swaps, standard axioms only.

Native `coefficient-writes-v2` checks every output limb and paired tower-call
argument/order for arbitrary 26 inputs and arbitrary paired tower answers,
and checks the static schedule against the symbolic formula. Exit 0, 4.921 s,
586132 KiB, zero swaps. The first harness fails only on array-equality memcmp
unwinding; replacing the harness's equality with explicit limb comparisons
fixes it. Two initial extraction drafts omit the copied field module files;
those Rust compiler failures are retained. The corrected release-mode owner
extraction succeeds. Rejected Lean drafts and retired preflight J10319 are
retained; no source/cap is retried unchanged. Existing tower, linear, Horner
and finish native gates are reused with their unchanged source pins.

## Stage 3b: all mask-column reads and selected-mask value

J10330 proves all 26 complete sparse MLE calls and their destination reads
without an MLE-output premise. J10331 composes those reads, the G-column MLE,
and the complete selected-mask caller. `claims_value` identifies each read
with `honestClaims t a 0`; canonical input arrays and their usual trace
representation are the inputs, not an output equality. The native full-context
column-loop gate checks all 26 outputs, all point operands and ordered column
handles, exit 0, 27.266 s, 1166888 KiB, zero swaps. Column handles stand for
read-only arrays; each complete array MLE's value is the separate Lean proof.
J10329's opaque-value conversion reaches default recursion depth; explicitly
unfolding only the named symbolic value at that proof step fixes it in J10330.
No recursion-depth or heartbeat setting is raised. J10331: exit 0, 1.78 s,
4086212 KiB, zero swaps, standard axioms. This is the semantic oracle's mask
component, not yet its extra-plus-terminal value or success theorem.

## Stage 3c: native basis and exact extra functional

J10338 constructs a concrete M31 subfield basis in QM31, and J10340
instantiates the complete mask-read theorem with it: no B.i/B.u representation
premises remain in `ProverCommitConcreteMask51.exact_result`. J10333/37 identify
the complete two reverse-Horner extra evaluations with the model Libra dot
product. J10341 gives `honestExtra` from explicit coefficient inputs (their
permutation provenance is addressed next). J10342 proves both native inverse
branches, including Some-success implying nonzero input; this is a local
arithmetic fact, not a full P_R1-source domain theorem.

J10343 proves symbolic hom transport of the entire mask formula. J10345 maps
the native basis to the retained `PrivacyR1AcctBasis.basis` in WideExact, and
J10349 transports all three statement points, all honest claims, and the
Libra/extra functional between fields. The first concrete extra-sum rewrite
fails at concrete instance inference; a generic Field lemma fixes it without
normalizing the carrier. Rejected conditional-simplifier drafts and missing
cache preflight J10344 are retained. The replacement reuses the cached account
basis rather than building an unrelated cold Session A dependency closure.
All accepted axioms remain standard. None of these transport results is
promoted to the full terminal/oracle result.

## Stage 3d: coefficient provenance and complete linear oracle component

J10348/50 prove the complete independent owned 1024-cell coefficient producer
and its exact `coeffsOf AspisR1.rowEquiv` image. J10351 composes it with the extra
evaluator, discharging the coefficient input law of J10341. J10352/55 compose
the native mask and extra values on WideExact:
`ProverCommitLinearOracle51.exact_result` concludes exactly
`embed (decode z) = R0Z.PayloadSplit.maskLinear AspisR1.rowEquiv
ProverCommitWideBasis51.basis a mappedTrace`. It needs only canonical point/
column inputs and the ordinary input trace representation; no mask, MLE,
coefficient or extra output/model identity is a premise. J10355: exit 0,
2.41 s, 4207016 KiB, zero swaps, standard axioms.

The full native `Variant::coefficients` `from_fn` gate times out at 180.002 s,
exit 124, cgroup peak 3372949504 bytes, zero swaps. Its GNU-time RSS is only
15652 KiB because it measures the timeout parent; the aggregate cgroup peak
is retained explicitly. It is not accepted and is not rerun unchanged. The
loop trace isolates standard-library array construction and Kani's arbitrary
array creation. The narrowed row callback initially still enters array creation
and hits the harness unwind guard; removing that irrelevant array construction
leaves the arbitrary-index row kernel, which passes in 0.292 s / 128776 KiB.
The full owned Lean array result and native row kernel are established; a
complete native `from_fn` constructor refinement is not claimed from that
narrower gate. No new TrustedStd field is introduced.

J10354 proves the exact source half-inverse prefix's None iff alpha9=half,
Some-success implies alpha9!=half, and its canonical inverse value. The native
accepted-prefix control-flow gate (public-data/emit/convert/build/check and
panic rejection, with universal suffix outcomes) passes in 0.307 s / 137080
KiB, zero swaps. This does not by itself instantiate the complete P_R1 checker
or discharge its other source/domain obligations.
