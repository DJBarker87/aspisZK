# Stage 3 continuation: typed caller and selected sampler installation

ADOPTION CANDIDATE, branch `codex/cx-prover-rw-20261023`. Continues `dc479c23a0`.
Rust production checkpoint remains `9c131667ca`; no native source, verifier,
wire format, protocol or release target changed. No merge or push.

## Claims established at the first checkpoint

The full retained caller-005 emission now typechecks as `ProverRwFullFuns`,
parameterized by `ExternalTypes` and `ExternalFuns`. These are explicit data
parameters, not axioms or proved contracts. There are 28 type entries and 262
function entries. This does **not** instantiate the actual native dictionary.

`R1Z.ProverRwFullSampler.install` installs the actual selected sampler in entry
248. `total` concludes its success and the selected `SemSource.semChal` equation
for every block; only nominal field coordinates are copied. All other entries
remain parameters. `ProverRwFullSemantic.from_read` consumes that entry in the
actual full-caller `host_wire.SemanticTranscript.semantic`: the block is the
one returned by that caller's `sample_block`, and the returned transcript state
is preserved. It retains explicit row-range and successful-read premises;
it does not prove parser success, hash totality, or whole-row correctness.
`invalid_row` establishes the actual invalid-row result without a read premise.

`ProverRwWireTransport.sample` proves exact nominal transport of the projected
selected validated block reader to `ProverCommitSemanticProgram28.sample`,
with the same digest callback, including row-order errors, failure/divergence
and the full returned state. `wire-projection.json` pins the exact declaration
blocks in caller-005. The projection is not a new Aeneas extraction.

`ProverRwRetryModel.retry` binds the **actual rewritten emitted recursion** to
`ProverCommitRetry34.run` for `k.val + fuel = 8`. The model retains callback
state across retries, projects it away only at return, and keeps the complete
returned durable store. Only body `Rejected` retries; entropy `Rejected`,
other errors, failure and divergence stop. The actual per-attempt body remains
inside the model attempt; this does not discharge R2/R3, PrefixContract,
BodyContract, entropy laws, filesystem semantics, or a security-experiment join.

## Backend adaptations and trust boundary

`adapt-caller.py` records raw and normalized hashes and all template signatures.
The raw full Funs is not claimed to typecheck. Adaptations are:

- replace template axioms by typed dictionary fields; retain all emitted bodies;
- name 16 enum discriminant instances explicitly, preserving their codes;
- expose unsupported F64 and Formatter carriers as extra type parameters;
  recreate Debug's typed carrier rather than import `core.fmt.Formatter`;
- expose File `write_all` as one additional **unproved** external entry;
- expand recursive PartialEq defaults; `neq_default` proves their Bool law;
- qualify `Aeneas.Std.lift`, avoiding capture by `host_semantic.lift`;
- normalize 20 wrapping-shift count APIs to U32 (constants or explicit cast);
  `low_count` proves modulo preservation when the width divides 2^32, but
  installation at every normalized native call is still a refinement obligation;
- specialize the duplicated SHA FixedOutput wrapper BlockSize/ArrayType carriers
  to Rust's single inherited associated types. The emitted unconstrained pair
  is ill-typed; no equation for arbitrary unequal carrier types is asserted;
- normalize owned FnOnce/FnMut closure result shapes and identity backwards
  continuations, and the final two-component store return. `owned_callback`
  proves the generic identity-backwards equation; this is not a compiler theorem;
- inline the backend unwrap result cases, retaining success/panic results;
  exact runtime panic diagnostics/effects are not newly certified;
- replace 33 default `toStr` native length proofs with explicit kernel proofs
  of the one-/five-byte literal bounds. `ProverRwStringBounds` was tested first.

No generated heartbeat/recursion overrides were retained in the new full
translation. The existing retained sampler normalization is unchanged.
No whole native/emission equivalence theorem follows merely from these repairs.

## Validation and evidence

Receipts and source snapshots are under the existing `stage3/` evidence folder;
`continuation-summary.json` distinguishes actual compiles, launcher refusals,
elaboration failures and failed **axiom audits**. At this checkpoint there are
48/100 total Stage 3 Lean compiles (36 new), 42/60 total Kani runs (none new).
Next ID 11250; 52 Lean compiles remain. No unchanged native regression is rerun.

11249 audits the full parameterized caller and selected semantic installation:
exit 0, 1.76 s, 4,200,852 KiB peak RSS, zero swaps, all twelve audit statements
use only a subset of `[propext, Classical.choice, Quot.sound]`. Retry control's
11247 and adapter facts' 11248 audits also use only that subset. Every target,
source hash, dependency fingerprint, source revision and full axiom block is
retained. Elaboration logs with sorryAx and the otherwise successful 11226
(Formatter axiom) and 11235 (33 backend native-decide axioms) are rejected proof
evidence and retained. The accepted replacement is 11249.

Only this branch's new module names are overwritten; preceding sources/objects
were snapshotted under the branch-named host stage3 snapshots before changes.
No pre-existing project proof module was overwritten. Dependent needed modules
were rebuilt after input changes. The old direct-import fingerprint failed to
detect a changed transitive dictionary carrier because the intervening .olean
bytes were unchanged. Launches 11217 and 11230 were refused, not compiles.
The runner now fingerprints the transitive source-import closure and resolves
base objects through env J; it does not salt fingerprints or bypass the launcher.
The stale inherited revision.txt in 11212–11215 is disclosed and corrected in
the summary (actual starting base dc479c23a0); exact input source hashes remain.

Caps remain Lean -M7000, MemoryHigh=5G, MemoryMax=7G, MemorySwapMax=0,
TasksMax=64, one Lean thread. All observed reservations were within the 55 GiB
host limit. The audit records a populated 24 GiB reservation. No absolute timing
run is authorized while peer capped jobs are populated, so none was launched.
Historical differential/relative timing/ELF receipts are reused, with no new
native coverage, quiet-host speed result, adoption or frozen-manifest replay.

## Next obligations

Install the concrete remaining type/function representations and their source
contracts, including hashing/ROM, samplers, field/weight/geometry kernels, IO,
parallel evaluation and P_R1. Complete the per-attempt model equation, and the
native compiler connection for normalized emission. Bind the selected caller's
entropy/reservation/serialization path and its PrefixContract/BodyContract.
Then prove the unchanged real experiment/observer/oracle RunJoin with E1/E2
and joint L1/L2 coupling. No privacy premise or security target is discharged.

## Second checkpoint and demonstrated false refinement statement

The stop condition is a **proved false unrestricted pure-dictionary E1
refinement**, not exhausted resources or a timeout. Privacy itself is not
refuted. The 100-bit target and the original realBad/realSeedQueries are unchanged.

The native `StateOnlyAttemptSecrets::generate_for_mask_nonce`
(`crates/aspis-prover/src/state_only_entropy.rs:211–238`) creates a **new zero
64-byte buffer on every entropy iteration** and calls `getrandom::fill`.
For any admitted nonzero public nonce, the raw E1 tape with first block all
zero and second block all byte 1 retries once and then has both nonzero
32-byte secret halves. The limit is 16. This is an allowed tape, however rare;
no new conditioning or bad event excludes it. This source-control example
is not claimed to be an actual OS RNG experiment.

The emitted external signature is instead pure:

```
getrandom.fill : Slice U8 → Result ((core.result.Result Unit getrandom.error.Error) × Slice U8)
```

A fixed `ExternalFuns.op129` has no RNG cursor/world state. The same zero input
cannot return zero on one call and a nonzero block on the next. Lean proves:

- `ProverRwEntropyObstruction.no_two_draw_dictionary`: no dictionary satisfies
  those two concrete fill-result equations at the same input.
- `ProverRwEntropyIteration.same_iteration_shape`: for the **actual full emitted
  entropy body**, any two indices below the limit have equal fail/div/error/
  success-versus-continue outcomes after erasing only the continue index.
- `ProverRwEntropyIteration.no_retry_then_success`: consequently, no fixed pure
  dictionary can have the actual first iteration continue and a subsequent
  below-limit iteration succeed. It quantifies over every dictionary, nonce
  and returned secret. Its only domain premises are the two limit bounds.

This directly rejects the statement “a fixed pure external dictionary faithfully
represents every native E1 iteration and ordered fill-result history for every
admitted fixed coin tape.” `entropy-obstruction.json` pins the native function,
input buffers, raw/normalized emitted body and the exact counterexample. The
entropy body differs from initial parameterization 11224 **only by qualification
of `Aeneas.Std.lift`**; the obstruction was not introduced by changing its control.
The `effectful_two_draws` theorem exhibits the simple cursor-based alternative.

An implementation of a deterministic SHA hash may be interpreted purely;
fresh OS entropy cannot be installed as this pure callback with the asserted
unrestricted per-iteration law. The ROM and filesystem boundaries likewise
still need their explicit effects addressed; no new theorem about their native
interpretations is claimed. Do not bundle this impossible equality inside
PrefixContract, BodyContract or a leaf-contract record.

### Independent obligations completed before stopping

`ProverRwCallerBinding` installs structural Variant equality alongside the
selected sampler. It proves S2 admission, early Semantic rejection for S1/D,
and the actual `prove_masked_retrying_with` equation to the existing eight-run
model. The per-attempt body and all uninstalled dictionary entries remain visible.
There are now 260 uninstalled function entries, plus all 28 type representations.

`ProverRwSaltLoop.loop_finite` symbolically refines the actual counted salt loop
for every representable count and the invariant `index.val + fuel = count.val`.
`error_suffix` and `loop_eager` remove the source's inert counter-only suffix
after an inner error: the same returned status equals an eager-stop model,
without assuming successful derivation, allocator success or salt correctness.
This is not yet the model's cryptographic salt-derivation equation or an L2 law.

### Final focused evidence and remaining work

Final audit 11261: exit 0, 1.69 s diagnostic wall time, 4,266,180 KiB peak RSS,
zero swaps, thirteen axiom reports all within `[propext, Classical.choice,
Quot.sound]`. The 11256/11257 heartbeat failures and 11258 failed local-reducibility
experiment are retained and rejected; no limit was raised. 11260 proves the
iteration result by symbolic shared-prefix congruence and case splits, without
unrolling sixteen entropy attempts or evaluating concrete byte arrays broadly.

There are **60/100 total Stage 3 Lean compiles**, 48 in this continuation,
with IDs through 11261 and two refused launches. **40 Lean compiles remain**;
Kani remains **42/60**, with no new runs. Next ID 11262. No budget exhaustion
is claimed. `final-environment.json` verifies all 887 final-audit dependency
objects unchanged and pins 25 branch modules; `continuation-summary.json`
checks their accepted final source hashes against repository files. Revision
abbreviation `d735d8174e` in second-checkpoint inputs is resolved explicitly
there to `d735d8174e6cdcc22eff9803ac4ac5cb6687f7b5`.

The final quiet-host preflight exits 78 because peer capped jobs remain;
no absolute prover timing was run. Rust and verifier files are unchanged;
previous differential/ELF evidence is reused, with no new runtime gate claim.
No full frozen replay is justified while this native interpretation is open.

Next concrete deliverable: an effect-aware interpretation of the entropy owner
whose read64 boundary returns updated RNG/world state, connected through the
callback and retry owner. Replay the zero-then-nonzero tape with both ordered
reads retained. Alternatively, prove a sufficiently weak observational
transport, including its unchanged bad-event/probability law and joint L1/L2
observations; do not silently replace the fixed-tape contract or assume the
transport. Then complete the remaining pipeline components, actual
PrefixContract/BodyContract instances, native compiler/runtime connection and
experiment/observer/oracle RunJoin. **Conjunct 1 and the security target are not
yet established.**
