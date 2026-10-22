# Prover commitment continuation 34

Branch: codex/cx-prover-commit34-20261022. Actual base: 0583e6bd5 (D146);
requested research pin: 26b922be6. Stopped at the concrete runtime entropy/reservation law; target not yet established.

## Scope statement

D146 restricts the statement domain to images of shipped `r0::Public` values
whose `public_bytes` returns `Ok`. This restricts statements, not adversaries
or oracle queries. D143 observables are public statement bytes, proof bytes,
and answers to adversary queries. Timing and other side channels are outside
the privacy contract. No endpoint premise has yet been removed.

Announced quantifier before:
```lean
∀ x : R0Z.ZkStatement.Statement K CommitHandle, ...
```
Announced quantifier after (scope statement; domain constructed, endpoint not specialized):
```lean
∀ x : {x : R0Z.ZkStatement.Statement K CommitHandle // R1Z.ProverCommitDomain34.DeployedStatement x.1}, ...
```
These are the domain quantifiers only; the complete endpoint before/after is
recorded when its specialization is implemented. The existing endpoint is
unchanged at this checkpoint.

## Stage 1: serializer and domain

The existing serializer dependency cone is now recompiled in Env J (J9053–
J9060), using the existing pinned generated definitions with import paths
ported. Computational definitions are unchanged. `serializer-source-pins.json`
compares `public_bytes`, `private_public`, and `withdrawal_public` verbatim
against extraction source revision 781929374. This is reuse of historical
extracted code, not a new owned-reference extraction contrary to D144.

`ProverCommitDomain34` (J9066) fixes a field-preserving source image into
`R0P.Public WideExact`, including exact source live u64 index and both
frontiers. `DeployedStatement` quantifies over the **actual extracted Public**
carrier and successful extracted `public_bytes`, not a handwritten admission
predicate. `lower_image` proves a canonical source projection has a left
inverse. `source_bytes_exact` proves every successful representative returns
one fixed model byte function, without choosing a source from the output.
`public_bytes_ok` proves existence of a representative returning exactly
`ok (.Ok (sourcePubBytes x))` on the announced domain. The source success
result also proves all serialized raw words canonical. No withdrawal-nonzero
restriction or truncation is introduced. `sourcePubBytes` has its vector
bound proved symbolically (at most 1455 bytes).

`outside_no_serializer_success` proves that a source representative outside
the domain cannot return any successful public serialization. This is not yet
a theorem about the full retry/proof-producing caller: that caller can first
return an entropy error, and Aeneas failure/divergence must not be silently
renamed `Error::Semantic`. No new API accepting arbitrary wide records has
been invented. The source-to-runtime boundary remains P6; this is one-kernel
composition of extracted definitions, not a new claim of Rust semantics.

## Verification

Env J starts after part 33 J9052, within 9000–9199. Host jobs use individual
6G/8G/zero-swap/64-task scopes. No shipped file has changed.


Stage 1 checkpoint: J9061–9062 and J9064–9065 are rejected proof drafts;
J9063 accepts the intermediate domain, superseded by J9066's exact source
vector result. Accepted axioms are subsets of [propext, Classical.choice,
Quot.sound]. Full source snapshots and raw receipts are in
`evidence/prover-commit34-20261022/lean`. No shared existing module/object was
replaced: ported serializer modules use new module paths. The historical
namespaces retaining `431` are composed here under Lean 4.32, not by mixing
kernel objects.


## Stage 2: extracted retry control and native caller gate

`AspisR1Retry34.owner.retry` is a newly extracted structural recursion over
owned state and a decreasing counter, with one arbitrary effectful policy.
There are no loops, iterators, BTreeMap, RefCell or timing calls in this
reference. Charon reports `has_errors=false`; Aeneas exits zero. Its
`ProverCommitRetrySource34.eight_source` theorem (J9085) transports the extracted
owner into the stateful eight-attempt model, including all early outcomes,
backend failure/divergence, returned attempt count and retained state. The
policy can retain the complete adaptive oracle history. Usize arithmetic is
proved nonwrapping over the eight-attempt range.

The Kani gate `proofs::retry_eight` checks the **verbatim entire** shipped
`prove_masked_retrying_with` caller against that recursive Rust owner on all
eight steps, not one sample transition. Proof/entropy/reservation callees are
explicit substitutes. All error tags and arbitrary byte-valued proof/audit
outputs, arbitrary u64 state transitions and ordered call logs are compared.
The native loop never inspects the proof/audit data. This control result does
not certify proof assembly, field arithmetic, actual OS entropy or actual
filesystem reservation. Source correspondence of each callee is still needed
to install a concrete whole-prover policy.

A critical origin distinction is retained: `next_attempt(k)?` aborts even on
`Error::Rejected`; only `prove_masked_attempt`'s Rejected causes a retry. A
single error tag without its origin is insufficient. `Step.retry` and
`Step.stop error` keep this distinction. The separate native Kani gate
`proofs::entropy_rejected_aborts` also passes. No shipped change was needed.

`ProverCommitRetry34` (J9077) installs the actual extracted serializer guard,
proves `outside_nothing_published` for the stateful controller independently
of arbitrary downstream proof constructors, and transports the certified
native walk before an arbitrary stateful publication continuation. Thus
invalid/outside source representatives cannot reach proof construction;
source entropy errors can stop even earlier. Backend failure/divergence is
preserved as such, not renamed a Rust Error. This remains a source-control
composition at P6, not a complete native publication callee certificate.
The transported part-33 map loops are not yet a complete publication policy.

The first native Kani draft (`retry-eight-v1`) has an unwinding-assertion
failure in generated whole-struct `memcmp`, not a source counterexample.
The replacement (`retry-eight-v2`) compares every field and every call-log
entry explicitly; it passes without suppressing unwinding assertions or
raising the memory cap. Both receipts are retained.

Composing the old serializer extraction with the main source cone exposed a
historical attribute-generator collision (`instDiscriminantErrorIsize`,
J9067). The copied serializer Types now uses explicitly named, namespace-local
instances with identical tag values; computational serializer definitions
remain unchanged. J9068–9075 rebuild its entire dependent cone, and J9077
then composes successfully. Snapshot-before-overwrite applies to this job's
own newly installed objects; no inherited shared module was modified.

## Stage 3: entropy events and demonstrated law boundary

`ProverCommitEntropy34` (J9088) defines separate `osBad` and `zeroBad` events
and exact `osMass`/`zeroMass` for any specified finite runtime law. They are
disjoint and `failure_mass` proves their sum is the complete entropy failure
mass. `uniform_zero_mass` proves the conservative bound
`3 / 2^256` for sixteen-draw exhaustion on the stated uniform raw carrier.
It uses the necessary first rejected 96-byte draw and the union of its three
zero 32-byte slices; it makes no independence claim about later draws and
does not pretend this upper bound is the exact sixteen-draw probability.
`eight_failure_mass` gives `8 * (δos + δzero)` for specified per-attempt
masses, without inter-attempt independence.

`no_universal_os_bound` proves a concrete obstruction: the source entropy
transition type and retry control alone imply no OS-error bound δ < 1.
The always-failing first OS call is a consistency witness, with exact mass 1
(`always_os_mass`). This is not an assertion that deployed getrandom always
fails, and does not refute privacy on its actual law. It refutes replacing
the missing runtime entropy law by uniform/error-free draws without a premise
or an explicit abort transport. The existing endpoint's fixed bad-event and
error budget cannot absorb an arbitrary unit-mass OS failure by definition.

**Exact next interface:** a concrete joint runtime entropy/reservation law,
including initial durable-ledger state and all `getrandom::fill` outcomes,
which either transports source errors to the model's existing failure view
with matching law, or proves their inclusion and mass inside the endpoint's
already nominated bad events. It must retain the successful reservation
before mask/salt derivation, all rejected-attempt ledger updates, duplicate
nonce errors and write/fsync failures. This is a missing source/environment
refinement, not a new cryptographic assumption or a proposed TrustedStd field.
Actual source points are `state_only_entropy.rs:172–196` (generate),
`:919–962` (reservation/create/write/fsync/fail-closed), and
`prover.rs:354–375` (retry). No numerical OS or filesystem failure law is
provided by these functions or by the inherited proof interfaces.

Stopping at this interface rather than silently adding a new δ term or an
error-free-OS premise to the endpoint. Independent stage-1/control/entropy
results above are retained. Stages 4–5 remain open: no actual source-to-
FSExperiments instance, no shippedProverExperiment, no concrete real/ideal
WholeRunJoins, and no deletion of RustProverRefinement. Full native simulator
publication (proof bytes, ordered tables, merge and early errors) also remains
a concrete callee obligation; a generic retry policy does not discharge it.


## Actual endpoint before/after

The actual endpoint is unchanged from 0583e6bd5. Full byte-identical before/
after modules and the empty diff are retained under `endpoint/`. The announced
D146 domain quantifier is shown above; it has been constructed in Domain34,
but no completed endpoint specialization is claimed. All existing premises,
carriers, failure events, budgets and conclusions remain present. In
particular, zero premise deletions are reported.

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


## Final validation and unchanged shipped target

J9090–J9095 rebuild the focused domain/retry dependency cone after replacing
word-size positivity reductions by symbolic `Nat.two_pow_pos` witnesses.
J9095 is the final axioms audit, exit 0, wall 1.69 s, peak RSS 4,131,808 KiB,
zero swaps. The largest accepted Lean peak is 4,172,480 KiB (J9094). Exact
commands, targets, attempt numbers, source overlays, dependency fingerprints,
exit statuses, times, peak RSS, swaps and complete multiline #print axioms
are in `lean/attempts.json` and raw receipts; `final-proof-audit.json` checks
final host source/object identities and the entire retained dependency pin
list. Historical source-base revision 0583e6bd5 plus exact overlay hashes is
recorded explicitly, rather than attributing new proofs to unchanged source.

The native eight-attempt Kani gate exits 0 in 15.708 s, peak RSS 772,412 KiB,
zero swaps; the entropy-Rejected gate exits 0 in 1.023 s, peak 164,472 KiB,
zero swaps. Charon/Aeneas both exit 0 (0.276 s / 149,072 KiB and 0.232 s /
57,904 KiB respectively; zero swaps). All tool commands run in individual
MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64 scopes. Rust linker
flags are `-C link-arg=-Wl,--threads=4`. Kani uses its dev-profile MIR pipeline
for bounded control verification, not a debug arithmetic gate. Extraction
uses --release; no dense finite-field work is run. Raw and aggregate cgroup
metrics and tool/source hashes are retained in the receipts and input pins.

`TrustedStd` is byte-identical to the base. No std field or cryptographic
assumption was added. No files under crates/ or programs/ changed;
`shipped-sources-unchanged.json` records the assessment. Thus the three-ELF
rebuild rule is not triggered. No full frozen manifest is replayed because the
concrete source-refinement preflight is not green; the one final focused audit
is not presented as a release replay. No unrelated runtime/adversarial suite
was repeated. No local target directory, wallet or key was created or deleted.
All this job's host processes have completed; caches remain retained.
Nothing was pushed, merged, or written into another worktree.

**Target not yet established.** The next concrete deliverable is the joint
runtime entropy/reservation law named above, followed by the complete native
publication policy and source-to-FSExperiments observation conversion. The
current partial results justify neither WholeRunJoin nor removing
RustProverRefinement.
