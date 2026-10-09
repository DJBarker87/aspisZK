# Same-body execution, commitment cuts and recorded C1 access

Parent: `9e65594156c06b53a2ebea2041a9662850d6bbb8` on the isolated
`research/v8-completion-fs-extraction-20260911` branch. This continues the full
formalisation/soundness objective; it does **not** mark it achieved.

## Constructed now

The ten-module `CompletionSourceAudit` closure replaces several previously
external values with explicit source-shaped computations:

- `SemanticWireExecution` computes the carried semantic scalar through ten
  compact rounds from one 697-field word. It constructs the literal 84-field
  terminal projection, excluding the three D lanes as the source does.
- `SameBodyOrdinary.prepare` constructs gamma batches, shifted kappa row scales,
  inactive claim/uncorrected ordinary scalar, OOD interpolant and chord inputs from the same word.
  Inverse failure remains failure. The public-weight affine correction is not
  implemented by this constructor yet.
- `SameBodyRelation.produce` serializes a legal nested reply strategy into the
  fixed-field layout. `produced_consumes` constructs trace consistency without
  requiring an externally supplied coherence certificate. This is model trace
  consistency, **not** an additional Rust verifier check.
- `SameBodyAssembly` connects those constructors: every legal later continuation
  preserves the semantic computation and ordinary/OOD preparation, including
  inverse rejection, because earlier consumed fields are preserved literally.
  The source comment's phrase “inverse/domain rejection” refers only to the
  fallible coordinate inverse: this constructor does not establish secure-circle
  membership, distinct OOD-domain points or the remaining sampling guards.
- `FSBoundedTranscript.constructBoth` runs both commitment-building scripts in
  one cached, full-answer oracle history. `constructed_cuts` derives nested
  post-construction/pre-absorption C1 and C2 cuts. Builder calls, aborts and
  repeated answers are not discarded.
- `FSExposureOrder` addresses the distinction between verifier replay order and
  original oracle exposure order. An actual linked absorb/squeeze pair either
  has the required first-exposure order, or the absorbed full answer was already
  a target extracted from an earlier squeeze-query input. This is a deterministic
  classification, not yet its random-oracle probability charge.

The semantic and ordinary constructors still expose arithmetic interfaces and
realised earlier challenges. They do not assert those interfaces are the actual
QM31 machine implementations or that the challenge law is uniform. No theorem
here assumes an accepted payment or a successfully recovered witness.

## Source and executable evidence

`source_transcript.rs` compiles unchanged core field, transcript and selected
state-only polynomial evaluator modules. The semantic control's round assembly
is a source-shaped transcription of `performance_verifier::semantic`, not an
Aeneas translation of that entire function. Executable Lean and actual selected
Rust scalar kernels agree on 32 M31 and 32 full-QM31 ten-round executions.
The independent Lean arithmetic uses direct complex/extension multiplication;
Rust uses the actual optimized prepared/fused kernels. This is differential
evidence, not universal field-kernel refinement.

The same executable checks real absorption/squeeze/advance inputs, bounded
sampler exhaustion and restored cache hits. C1/C2 builder controls distinguish
the pre-absorption cuts from the later transcript calls: with one synthetic
hash call per builder the cuts are 1 and 7, the final log has 8 calls and only
6 fresh answers. These are full-answer synthetic oracles, not SHA256 tests or
complete valid-payment proofs. Latest combined evidence:
`results/v8-completion-fs-extraction-20260911/semantic-4zu5a9mg/`.

The relation and ordinary model fixtures also passed five and ten controls,
respectively; the agent report records their commands and exact scopes.
See `same-body-agent.md` and `fs-agent.md` for full premise/source maps.

## New bounded recorded-access implementation

`ExtractionRecordedC1.rs` produces the existing authenticated first256-fibre
opening input from a finite frozen raw-input/full-answer prefix. There is no
witness, pre-encoding table, honest anchor or oracle callback argument.
It performs 521 recorded-node lookups and obtains ten off-path sibling digests.
Missing, forward, noncanonical, inconsistent, colliding and over-budget data
remain explicit failures. The original authentication source slice accepts the
positive bundle and returns 16,384 semantic **evaluation** scalars using only
cached recorded answers. It does not return message coefficients or a witness.

The payload is 111,620 bytes, plus 1,024 bytes for explicit indices and container
overhead; these are extractor-local data, not additions to the submitted proof.
The existing large inverse-matrix precomputation/solve was not replayed. This
closes an access API predecessor, not low-agreement list decoding or availability
of the required recorded window on every accepting execution. Full details and
15 failure controls are in `extraction-agent.md` and its retained evidence.

## Clean proof-artifact validation

The smallest leaves were checked first. A separate Lean 4.33.1 environment was
then installed on the authorised NUC without modifying historical 4.32.0.
Ten first-party modules were rebuilt from the exact copied sources into an
empty artifact directory. No historical Aspis `.olean` was substituted.
Toolchain/Std distribution artifacts were reused, not source-rebuilt.

The explicit root was then checked with:

```text
lake env leanchecker --fresh -v CompletionSourceAudit
```

Both stages ran under finite `MemoryHigh=6G`, `MemoryMax=8G`,
`MemorySwapMax=0`, `RuntimeMaxSec=600` cgroups. Rebuild exit: 0. Fresh replay
exit: 0, wall 64.90s; time-tool peak RSS 974,032 KiB; swaps 0. This is replay
through Lean's own kernel, **not** an independently implemented external checker.
All printed promoted axiom lists contain only the established standard
foundations. Root signatures and full commands are retained.

Evidence: `results/v8-completion-fs-extraction-20260911/nuc-clean-20260912/`.
Its manifests contain source hashes, direct import resolution, new artifact
hashes, compiler/checker binary hashes and checker-source hash. The closure
covers these new prerequisites only, not the historical V8/Mathlib dependency
graph or global residual theorem.

`KernelBuild.py` reproduces the bounded Linux source-build and replay stages.
It refuses non-Linux/uncapped/positive-swap scopes, nonempty first-party build
directories, changed sources/artifacts, or a mismatching toolchain. Use a fresh
work directory for `--stage build`, then the same directory for `--stage replay`.
It never probes `leanchecker --help`.

## What still prevents the requested global result

1. The old complete-wire theorem still accepts an independent `Program`.
   These new constructors must be connected to the actual complete parser,
   public/runtime context, exact profile, public weights, checked query increment,
   terminal equation and authenticated phase words. Literal Rust operational
   refinement is still missing. It is not a small numerical error probability.
2. Legal typed strategies are not yet constructed uniformly from every real
   adversary/source execution, including offline prequeries and transcript
   selection. New first-exposure order/cut results help; they do not themselves
   provide this coupling or its resource/extraction theorem.
3. `RecoveredHigh` is algebraic recovery, not checked-payment extraction.
   Keep `A ∧ H ∧ R ∧ ¬X` in the failure event. Recorded access availability,
   efficient candidate enumeration and source semantic/copy/settlement validity
   remain unbounded obligations; none is silently removed by family membership.
4. Full-view adaptive ZK, global probability composition and all-reachable
   complete-transaction CU are separate unfinished gates.

Review found that `LogConsistent` alone proves log→cache coherence, not
cache→logged completeness. `FSFirstFresh` now constructs both directions and
the fresh-flag invariant from an empty-state execution. Its
`linked_fresh_order_from_empty` theorem derives freshness and the
order-or-premature-target alternative from the bounded script run, without a
caller-supplied cache-coherence or freshness premise. The unlogged-cache
counterexample remains as a regression. This is not yet a uniform random-tape
law or actual-source/adversary coupling.

This additional leaf was compiled after checking every imported first-party
artifact against the clean-build manifest; the unchanged ten-module source
build was not repeated. `leanchecker --fresh -v FSFirstFresh` then passed,
exit 0, wall 63.55s, peak RSS 969,388 KiB, swaps 0, under the same caps.
Its printed axioms are standard only. `freshness.json` and both logs retain
the source/artifact hashes and commands. `FreshnessBuild.py` reproduces this
extension against the preceding clean build. Thus eleven distinct first-party
modules were source-built in these two stages, not the historical whole V8
proof graph.

## Decision

No protocol, wire format, acceptance rule or production source changed. The
maximum proof body is still `697*16 + 52 + 24 + 22*621 + 2*296*26 = 40282`.
No CU/proving benchmark or new global security number is claimed. Grinding
security credit remains zero. Review was self-review plus agent premise review;
neither substitutes for independent cryptographic review.

The most important next integration is the full same-body semantic/ordinary/
authenticated-relation constructor into `SuccessfulAt`, with literal source
producers for every remaining field. In parallel, connect the derived
first-exposure invariants to the actual source distribution and close
candidate-to-checked-payment extraction. The full objective remains active.
