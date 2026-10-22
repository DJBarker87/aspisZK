# Part 50: native simulator continuation

**Target not yet established.** Branch `codex/cx-prover-commit50-20261022`.
Authorized Lean budget: J10200–J10299 only. Work proceeds through the six
interfaces in part 49, stopping at native payload equality, before any
FSExperiments conversion or joins.

## Frozen inputs and scope

Task base is recorded in `evidence/prover-commit50-20261022/pins/revision.txt`
under `docs/research/100bit-spend-path-20261013/`. No shipped file is changed.
Retained release ELF pins: default 40dc7574…, devnet 12cb0bc2…, Pool 121f3e29….
No fresh ELF build is claimed. Shipped code is never extracted by Aeneas;
independent owners and native transition gates provide the binding route.

## Endpoint before/after

The entire deployed endpoint is preserved verbatim in `endpoint/before.lean.txt`
and `endpoint/after.lean.txt` in this task's evidence. The snapshots are identical.
`RustProverRefinement` remains an explicit premise, with unchanged x/rust
quantifiers, failure event, conclusion and bound. No premise removal is claimed.

## Validation

Focused Lean targets run only on the build host, one module per attempt.
All host tools use MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64;
Rust uses four jobs, release optimization, and
`RUSTFLAGS='-C link-arg=-Wl,--threads=4'`.
Exact source hashes, dependency fingerprints, target/status/wall/RSS/swaps,
source attribution and printed axioms are retained per attempt.

## Stage 1: component preparation and complete three-product value

J10203 proves `Prepare50.q`: all nine prepared coordinates are canonical and
are precisely the symbolic tower components, including CM `a+b` and QM
`c0+c1`. J10206 proves every entire three-input scalar accumulation and the
complete nine-total matrix. J10209 proves `Dot50.exact_result`: the independent
owned caller succeeds, returns canonical QM31, and decodes to
`∑ i : Fin 3, decode (x i.val) * decode (y i.val)` for arbitrary canonical inputs.
No prepared-coordinate, accumulator, or output/model identity is a premise.

Native preparation and all-27-product aggregation gates pass, with complete
output matrices; preparation also checks paired arithmetic operands and order.
The aggregation products are arbitrary bounded callee answers. Their integer
multiplication and canonical bound are separately proved by the retained
`NativeSquare49.mul64` and `ChannelSum49.product_bound`. This composes retained
part-49 channel transition/reconstruction gates with the new value proof;
it does not prove equality of the reordered complete caller's timing trace.
The prepared-multiplier path needed by the next interface remains next work.

J10200 was refused before compilation by the copied launcher's old range guard;
it is retired. The launcher now accepts only J10200–J10299 and retains global
Lean serialization and the 6G/8G/0/64 caps. J10202/05/08 are rejected carrier,
array-size inference and literal-index drafts; their replacement sources pass.
All accepted axioms are subsets of `[propext, Classical.choice, Quot.sound]`.
Focused receipts in `lean/attempts.json` record exact source attribution,
source/dependency fingerprints, target/status/time/RSS/swaps and axiom lines.
No shipped file changed; no deployed endpoint premise is removed.

## Stage 2: prepared multiplier and optimized evaluator

J10212 proves the full prepared constructor/multiply value path. Its row-input
representation premise is discharged by `caller`; canonical inputs suffice for
canonical output decoding to their product. The verbatim native constructor
and multiplication gate passes in 2.699 s / 213116 KiB, zero swaps, with exact
operation/operand traces for arbitrary matrices/RHS and universal paired
arithmetic answers. No prepared-output/model identity is assumed.

J10239 proves `ProverCommitEval50.exact_result`: the complete owned optimized
28-coefficient evaluator returns a canonical QM31 decoding to
`(ProverCommitInterpolationPoly48.poly 28 decodecoeff).eval decodea`.
It includes actual x²/x³/x⁴ construction, the three-product block, prepared
constructor/multiplication, and all six reverse iterations after block six.
J10213/24/29 prove generic polynomial grouping before tower specialization;
J10237/38 prove the final block and loop. The native complete seven-block
caller gate passes in 4.944 s / 266592 KiB, zero swaps. It compares all callee
operands and order on arbitrary full coefficients. Prepared storage is an
opaque handle in that caller gate; its full matrix interface has the separate
prepared gate. No arithmetic law is inferred from universal callee stubs.

Initial index drafts confused the `core.num` and `Std` wrapper names; explicit
wrapping/index equations fix them. J10217 is a retired missing-dependency
preflight, no compiler launched. The final concrete bridge initially hits the
default heartbeat limit. Its explicit-type diagnostic (J10232) identifies
powers elaborated over two definitionally equal field aliases with different
instance paths. Using the decoder's exact carrier in both block/loop binders,
and a generic Field bridge, fixes this. Both changed modules are recompiled
before their consumer; no old dependent is silently reused. J10239 exits 0 in
1.97 s / 4054204 KiB, zero swaps. Failed sources/diagnostics are retained;
no option/cap was raised. The rejected concrete helper is retained only in
attempt snapshots, not the deliverable proof tree.
All accepted printed axioms are standard. No pure std trust field or shipped
source was changed. The complete semantic oracle and later interfaces remain.
