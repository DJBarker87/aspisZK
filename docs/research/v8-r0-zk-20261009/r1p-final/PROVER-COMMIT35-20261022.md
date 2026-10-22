# Prover commitment continuation 35

**Target not yet established. Trust boundary: P7, TrustedStd (unchanged), E1 (OS RNG).**

D146 statement domain; D143 published-data scope,
excluding timing and other side channels. Intended trust list: inherited P7,
TrustedStd (unchanged), and D147 E1: successful OS RNG draws are uniform and
independent. E1 is a named environment hypothesis, not a Lean axiom.

Actual base: `6b5544772`; branch `codex/cx-prover-commit35-20261022`.
Env J9100–J9199 follows part 34 J9095. No shipped source changed.

## Stages

1. Byte-blind schedule and retained reservation state: proved in the abstract model; native environment law obstructed.
2. Native failure-path control gates and extracted reservation bridge: verified with explicit primitive/callee substitutes.
3. Complete native simulator publication: open.
4. Source-to-FSExperiments observation conversion: blocked at the source-environment law.
5. Concrete WholeRunJoins and endpoint: open; no premise removed.

No premise deletion or completed endpoint is claimed by this setup checkpoint.

## Stage 1 checkpoint

`ProverCommitEnvironment35` (J9102) implements the byte-blind schedule,
including Unix directory open. `ask_blind` excludes private ledger/coin state
from schedule decisions. `create_retained` retains a created nonce on every
write/fsync outcome. `fail_closed` and `failure_replay` prove the environment
prefix returns only the same error, independent of witness and arbitrary
successful continuations, with the complete resulting private state retained.
This is a model theorem, pending the extracted/native callee bridge.

The schedule's arguments contain only index, kind and previous statuses; RNG
bytes and all three file payloads are excluded by construction. E1 separately
specifies conditional uniformity of each successful 96-byte draw for every
prior context. No OS/fs failure probability or new TrustedStd field is added.

J9100–J9101 are rejected proof drafts, preserved verbatim. J9102 exits 0,
2.48 s, peak RSS 4,174,784 KiB, zero swaps; all printed axioms are subsets of
[propext, Classical.choice, Quot.sound]. Receipts and source overlays are in
`evidence/prover-commit35-20261022/lean`.

Native checks substitute byte-blind OS primitives and downstream arithmetic;
they certify control, not the standard library, OS law or field arithmetic.
The reservation/create/write/fsync functions and the full reserve-before-build
method are copied verbatim and SHA-pinned. Initial extraction command v1 had
an obsolete --start-from name (exit 101); corrected v2 succeeds without source
or cap changes. This is a command correction, not a memory-pressure rerun.

## Stage 2: native control and extracted reservation owner

`ProverCommitEnvironmentSource35.reserve_source` (J9122) composes the
extracted structural reservation owner with the schedule model for every
history and schedule, including duplicate/IO errors, Unix directory-open,
all write/fsync suffixes and the complete returned ledger/history state.
`finish_source` covers Unix and non-Unix source branches. The native Kani
`reservation_all_paths` gate compares the **verbatim** reserve_fallible and
boolean reserve wrapper against that same Rust owner, including last_error,
call order and whether the file was created. The native source remains
unchanged. The OS/path primitives are substitutes in Kani, not certified
standard-library internals and not a proof of their actual joint law.

The extracted Types file needed namespace-local discriminant instance names,
with identical tag values, to avoid the known generated global Error-instance
collision. No computational function changes in that adjustment. The first
owner's numerical match representation was replaced by equivalent Rust
if/else control after focused Lean elaboration failures; the replacement was
re-extracted and its native-owner Kani gate rerun (v3). Rejected drafts remain
in evidence; no cap was raised. J9107/J9108 were launcher refusals after an
upstream Types failure, not compiler replays; the collector records exit 67
and no compiler resource result for them.

The byte-blind native reservation check, OS-error-at-any-draw check,
sixteen-zero-draw exhaustion check and reserve-before-derivation check all
pass. Successful create is retained on every later write/fsync failure;
builder failure after reservation also retains it. The builder and hash are
explicit callee substitutes, so this is control certification, not arithmetic
or full mask-construction correctness. The entropy gate uses representative
zero/nonzero 32-byte blocks, not the E1 distribution.

`ProverCommitEnvironmentLaw35.E1_event` (J9123) derives exact uniform event
mass from E1 for every prior context, and `E1_zero_candidate` retains the
3/2^256 conditional zero-candidate bound. No OS/fs δ is introduced. These are
conditional component results, not a new claim of an unconditional runtime
law or a modified headline bound.

`ProverCommitEnvironmentControl35` (J9126) projects the detailed local
failure to the actual API's Entropy/Semantic tags. `public_failure_replay`
proves witness-independent public error equality; `retry_failure_stops`
proves the eight-attempt controller stops immediately at any such failure,
with the full resulting state retained and no later continuation evaluated.
It does not rename environment errors into retryable Rejected. The inherited
`ProverCommitRetry34.rejected_next` continues to retain all state updates for
actual retryable rejections. These control facts do not repair the native
filesystem law below.

## Demonstrated obstruction: status-only schedule versus native create_new

`ProverCommitLedgerBoundary35.no_status_only_create_law` (J9117) proves that
no function of (index, kind, prior statuses) implements create_new on a fixed
ledger with an occupied and a fresh path, for both requests. Its corollary
uses the identical history `[(rng, Ok ())]`: successful RNG status gives no
nonce bytes/path to the scheduler. Both nonzero nonce candidates are possible
under E1; neither is a zero-exhaustion case. A schedule fixed independently of
the successful RNG bytes cannot return both required statuses at that node.
Choosing a different schedule after learning the private draw would change
the stipulated environment strategy/law; it is not a justified transport.

The optimized native probe copies the **entire actual durable-store and sync
implementation verbatim**, uses real std filesystem calls and the repository's
locked sha2 0.10.9, and confirms this example. From one ledger containing
nonce [1;32], reserve_fallible([3;32],[1;32]) returns Ok(false), whereas
reserve_fallible([3;32],[2;32]) returns Ok(true). Their SHA-256 paths are
distinct (081f3d…0f240.burn and c4d5a9…3fb7e.burn). Both hypothetical calls
start from the same ledger: the first duplicate call does not change it.
The exact stdout, source pins and compile/run receipts are retained under
`evidence/prover-commit35-20261022`. The two files contain only fixed public
test data and remain on the host. No wallet/account key was created.

This is an obstruction to the **literal status-only source-environment law**,
not a counterexample to privacy and not a claim that an error must receive a
small probability charge. The Kani primitive substitute intentionally did not
check the request path, so its passing result cannot discharge this law. E1
says nothing that makes create_new path-independent.

**Exact next interface:** a faithful private filesystem transition
`create_new(initialLedger, reservationPath, scheduledFault)` that preserves
existing entries and forces AlreadyExists on a matching path, together with
its exposure rule. Recommended repair: keep ledger membership/path handling
private inside the environment and let the byte-blind adversarial schedule
inject failures around it. An alternative is to supply the reservation
address as an explicit public scheduler input, but that requires an explicit
observability justification; no secret seed or file payload may be exposed.
Either repair changes the literal interface specified in D147 and is not
silently installed here. No additional TrustedStd or filesystem trust field
has been invented.

Stages 3–5 remain open behind this source/environment boundary: complete
native simulator publication, source-to-FSExperiments conversion,
shippedProverExperiment, both concrete WholeRunJoins and removal of
RustProverRefinement. Stopping at a proved interface obstruction, not replacing
those obligations by callbacks, an error-free OS premise or a δ.

## Actual endpoint before/after: unchanged

The actual theorem remains byte-identical to the task base. Full before/after
modules, hashes and empty diff are retained under `endpoint/`. No restriction
of x or addition of the schedule has been installed into the existing
endpoint, because no concrete source experiment/join is available. Intended
quantifiers remain the announced D146 statement image plus arbitrary
adversarial environment schedules; no change of budgets, events, conclusions
or witness/adversary restrictions is smuggled in. E1 is a visible named
hypothesis of the new component-law theorems, not an axiom and not a claim
that the unchanged endpoint now includes a discharged runtime source law.

The following is the verbatim unchanged top theorem before and after:

Before:

```lean
theorem privacy_headline_deployed
    (refinement : RustProverRefinement template outputs x rust observer_program)
 :
    ZK_FSS h B outputs rust x (simE (R0Z.ZkStatement.HonestProver.transport h) B outputs x)
      (modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge) ∧
    modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge ≤
      1 / 2^109 + 1 / 2^137 + 1 / 2^454 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge ∧
    modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge < 1 / 2^100
```

After:

```lean
theorem privacy_headline_deployed
    (refinement : RustProverRefinement template outputs x rust observer_program)
 :
    ZK_FSS h B outputs rust x (simE (R0Z.ZkStatement.HonestProver.transport h) B outputs x)
      (modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge) ∧
    modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge ≤
      1 / 2^109 + 1 / 2^137 + 1 / 2^454 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge ∧
    modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge < 1 / 2^100
```

## Final verification and retained scope

J9127 is the single final focused axioms audit: exit 0, wall 1.87 s,
peak RSS 4,134,020 KiB, zero swaps. It imports all new proof modules and
prints axioms for every new top theorem; all are subsets of
[propext, Classical.choice, Quot.sound]. It also prints the E1 definition,
extracted reservation theorem and status-only impossibility theorem for
statement inspection. Exact targets, source SHA256 overlays, dependency
fingerprints, commands, status, wall time, peak RSS, swaps, source base
revision and complete raw compiler diagnostics are in `lean/attempts.json`.
Rejected proof drafts and launcher refusals are retained, not counted as
accepted formal results. The final read-only source/object audit records the
committed source revision and checks every retained dependency-object hash.
No inherited shared module was modified; replacements of this job's own new
objects were snapshotted in the branch-specific host directory first.

The final native-owner Kani gate exits 0 in 2.975 s / 237,240 KiB. The
byte-blind reservation gate exits 0 in 1.969 s / 174,868 KiB; OS failure
9.286 s / 575,996 KiB; zero exhaustion 8.658 s / 514,616 KiB; reserve-before-
derivation 1.915 s / 180,352 KiB. Charon/Aeneas v3 exit 0 in 0.162 s /
162,072 KiB and 0.293 s / 66,000 KiB. The real-std probe compiles optimized
in 1.359 s / 149,296 KiB and runs in 0.013 s / 1,936 KiB, both exit 0.
Every recorded job has zero swaps. Raw receipts include cgroup limits and
memory.peak; all jobs use individual 6G/8G/zero-swap/64-task scopes and the
requested linker flags. Kani uses its MIR verification pipeline rather than
an unoptimized arithmetic workload. No dense finite-field gate ran.

TrustedStd and the actual endpoint are byte-identical to the task base.
There are no changes under crates/ or programs/, so the three-ELF rebuild
rule is not triggered. No full frozen-manifest replay is attempted: the
concrete source/environment preflight is demonstrably not green. Unchanged
runtime, reproducible-build and adversarial suites are reused, not rerun.
The existing 3/2^256 zero-exhaustion allowance is not replaced by zero or by
an OS/fs δ. No endpoint budget or failure event is changed.

No binaries, .olean, LLBC, tarballs or ELFs are committed. No local target
directory was created. All task host jobs finished; compiled caches and the
fixed-public-data probe ledger remain retained. No wallet/account key was
created, deleted or modified. Nothing was pushed or merged.

**Target not yet established.** Next deliverable: the faithful private
create_new ledger transition/exposure interface described above; then complete
native publication, observation conversion, concrete experiment and both
whole-run joins. RustProverRefinement remains explicit.

Final source checkpoint: `e8d60ec27`. The read-only source/object audit checks
eight modules and every retained dependency hash against that commit and the
recorded exact source overlays. It performs no compilation or repeated
regression. `final-proof-audit.json` and `shipped-sources-unchanged.json`
record this check. Next unused Env J attempt is J9128.
