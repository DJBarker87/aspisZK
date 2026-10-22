# Prover commitment part 23

Base `cb9372b8f`; branch `codex/cx-prover-commit23-20261021`.

Target not yet established. This packet closes the named local and generic obligations below; it does not claim a whole-source refinement.

## Plan and evidence discipline

1. Single-thread TLS accessor contract, semantic simulation and trace gate.
2. Split Rust BTreeMap operations and finite schedule transport.
3. Adaptive fuel/history transport.
4. Concrete caller/policy assembly, then assess the two WholeRunJoins.

The receipt inventory has consumed 7000–7473. The first available candidate is
7474, checked against both out and sha receipts on the host. Only 7474–7499
will be used, with a fresh check at launch. Every Lean job is serialised by
the existing global lock, capped at 6G/8G/no swap/64 tasks. No concurrent-owner
module is edited. Host-only instrumentation will live under this evidence
folder, with production source prefixes pinned. No local crates/programs
source edit is currently planned.

## Stage 1 — single-thread TLS contract

`ProverCommitTLS23.schedule_simulates` proves equality of all access outputs
and the final selected-thread value for arbitrary finite schedules of closures,
under the explicit `SingleThreaded` premise. `read_after_store` proves the
requested last-store law, and `access_frame` preserves every other thread.
The semantics cover one live TLS key and exclude creation/destruction/thread
exit during the schedule. Closures may return error values; this theorem does
not suppress RefCell borrow errors or equate distinct keys.

**P6/runtime assumption:** the target's LocalKey service implements this
per-thread live-key store semantics. The prover invocation uses one thread,
with no trace-key destruction or thread exit during the invocation. On the
Solana path native byte tracing is compiled out; the native prover path uses
the one-thread assumption. This is a platform boundary, not a proof of libc or
Solana's scheduler. No concurrent-worker runtime module was changed.

`tls-single-v2` stubs only `std::thread::LocalKey::with` with a persistent
RefCell slot, leaving the shipped `trace::value` and `trace::take` bodies,
borrow checking, allocation and field serialization intact. Kani requires
three generic parameters, so the stub casts the slot to T; its admissible
instantiation is **only the exact trace RefCell<Vec<(u16,usize,[u8;32])>>**.
This gate calls no other LocalKey. The stub must not be installed globally
for other key types or keys. The gate checks one append followed by two
takes, arbitrary tag/index and zero field value. Exit 0, 4.977 s, peak
543452 KiB, swaps 0. It is not a whole simulator theorem.

J7474 is an excluded missing-library-lemma elaboration failure. J7475 passes
`R1Z/ProverCommitTLS23.lean`: exit 0, wall 0.72 s, peak 1412672 KiB,
swaps 0; all four complete axioms audits use only propext/Quot.sound.
Exact source sha/dependency fingerprint/revision are in the committed
`lean/attempts-7474-7476.jsonl`. `tls-single-v1` is an excluded generic-arity
compilation failure; both attempts and their logs are retained.

All Rust additions are host-only instrumentation; the repository's shipped
files are unchanged. Thus this stage triggers no three-ELF rebuild.

## Stage 2 — split map operations and write induction

`ProverCommitTreeOps23.writes_decode` proves an induction over arbitrary
write schedules against the existing universal TreeMap model. It retains
both the decoded final tree and every insertion's previous answer. Its
explicit hypotheses are universal insert-state and insert-previous laws.
`get_decode` transports a get contract to the retained list model;
`iterSteps_spec` and `tree_iteration` retain every unconsumed enumeration
suffix. J7476 passes: exit 0, 1.36 s, 2533348 KiB, swaps 0; all four
theorem audits use only standard axioms. These are operation specifications
and a conditional composition proof, **not** a Rust std implementation instance.

The previous stopped combined gate is not rerun. New host-only gates use
exact shipped BTreeMap<Vec<u8>,[u8;32]> types and check one queried byte at
an arbitrary index below 32 (all answer bytes remain symbolic):

- `tree-get-v1`: one entry, arbitrary one-byte key/query and arbitrary answer;
  get presence/value and retained length pass. Exit 0, 52.235 s,
  6315228 KiB, swaps 0. This completed while approaching MemoryHigh.
- `tree-iter-v1`: one entry, one successful iterator step and then exhaustion;
  exact key, selected answer byte and key length pass. Exit 0, 35.592 s,
  2620428 KiB, swaps 0.
- `tree-insert-v1`: two insertions, arbitrary one-byte keys and arbitrary
  old/new answers; tests previous answer and length, without get/iteration.
  Stopped at 6399311872 cgroup bytes. Exit 1, 377.322 s,
  6230832 KiB, swaps 0; excluded, no counterexample claimed.
- `tree-insert-leaf-v2`: proof shape changed to unwind four rather than 34,
  still with unwinding assertions. Stopped at 6536085504 cgroup bytes;
  excluded. No larger cap was used.
- `tree-insert-retained-v3`: additionally excludes the harness's final map
  destruction with mem::forget (the actual operation retains its map).
  Stopped at 6531129344 cgroup bytes; excluded. This disproves the working
  hypothesis that final destruction alone explained the formula growth.

The stop JSONs name only this worker's CBMC process and scope. Every gate
uses 6G/8G/no swap/64 tasks and the required RUSTFLAGS. The exact source,
command, status/wall/RSS/swap fields for **all** Rust attempts are in
`rust-attempts.json` and `receipts/`. The split insertion check is still a
demonstrated resource obstruction after two explicit formula-shape changes.
No successful universal insertion certificate or arbitrary-height library
representation proof is available. The one-entry get/iterator results do
not discharge the universal hypotheses of writes_decode. No map source
equation is installed from a finite fixture.

## Stage 3 — adaptive shared-oracle fuel law

`ProverCommitAdaptiveFuel23.adaptive_exhaustion` bounds a fresh all-zero
five-answer window whose addresses depend on arbitrary earlier answers,
including unmarked and cached reads, in one global memoized oracle.
`adaptive_union` charges 24 dependent adaptive instances at `charge` when
the answer cardinality is at least p. `source_exhaustion` exposes the exact
remaining obligation: the shipped source failure event must imply the
fresh marked all-zero event. No conditioning on a random start or
inter-instance independence is used.

`ProverCommitAdaptiveLaw23.Fresh` is a syntactic invariant over all branches:
only marked reads must avoid every preceding read; unmarked reads may
repeat. `lazy_exact` proves the exact expectation of every rational test
of the complete marked vector, and `fresh_uniform` proves its exact joint
uniform law under that invariant. This strengthens part 22's fixed-start
window law. The shared interpreter still retains every ordered address,
answer and repeated read; its existing exact-oracle law is reused.

J7477/J7478 are excluded eventMass elaboration failures; J7479 passes the
adaptive exhaustion/union module (3.85 s, 4035740 KiB, swaps 0).
J7480 is an excluded namespace elaboration failure; J7481 passes the exact
adaptive-law module (3.13 s, 3994416 KiB, swaps 0). Every new theorem has a
complete #print axioms result using only the standard three axioms. Exact
receipts, source snapshots, source revision and dependency fingerprints
are retained under `lean/`.

These are mathematical interpreter results. They do not assert source
reachability of the marked program, establish the caller's freshness
invariant, or construct a coupling whose extra retained Tape is independent
of the pre-existing model carrier. In particular `ProverCommitFuelJoin22`
is unchanged: its additional Tape cannot simply be defined by inspecting
its model's already sampled coins. The required joint independence and
both output marginals must still be proved for a concrete source adapter.

## Stage 3 addendum — complete ordered-history law

`ProverCommitAdaptiveHistory23.complete_joint` strengthens the marked-vector
law to **every rational test of the full ordered query/answer history and
terminal output**. It equates the one-uniform-complete-oracle expectation
with an interpreter supplied an independent marked vector, memoizing those
marked values for all later reads while sampling other first reads lazily.
Repeated reads, their positions/answers, errors, retry/abort outcomes and
final state may all be observed. No acceptance-only projection or history
reordering is used. The source-shaped Fresh invariant is a visible premise.
The proof's unmarked-fresh branch commutes independent expectations; its
marked branch uses Fin.cons to expose one coordinate. No universe is
concretely enumerated.

J7484 is an excluded missing induction-generalization failure. J7485 passes
both `lazy_joint` and `complete_joint`: exit 0, 2.06 s, peak 4020004 KiB,
swaps 0, standard three axioms only. Exact source/dependency fingerprints
are in `lean/attempts-7484-7486.jsonl`.

This closes the **generic joint adaptive-history law**, and strengthens the
previous partial fuel reasoning. It does not construct the shipped Marked
program, prove its Fresh invariant/counter room, or give the concrete
finite coupling/marginal factorization required by FuelJoin22.RunJoin.
Neither WholeRunJoin is inferred merely from equality of interpreter laws.

## Stage 4 — concrete rho policy and remaining caller boundary

`ProverCommitPolicy23.policy` replaces the extracted suffix's QM31 callback
with the actual previously proved source sampler and a reversible nominal
carrier conversion. `installed_total` supplies its output and exact selected
model meaning for every block. `rho_after_block` installs that output in the
actual extracted row-32 caller, preserving subsequent cast, embedding and
Vec-push errors/divergence. This discharges the **QM31 policy parameter** of
the owned suffix. Gamma, ordinary and query policies remain explicit; no
model-defined sampler is substituted for those source operations.

J7482 passes the initial four-theorem policy module. J7483 passes the
strengthened five-theorem module: exit 0, 1.95 s, 3955840 KiB, swaps 0,
standard axioms only. Exact source snapshots and dependency fingerprints
are in `lean/attempts-7482-7484.jsonl`.

`tls-programmed-v1` applies the same live-key single-thread contract to the
exact PROGRAMMED slot type, separately from the trace slot. The unchanged
source install/uninstall bodies pass an empty-table install, retained Some,
uninstall to None, and repeat-uninstall gate: exit 0, 4.219 s,
538884 KiB, swaps 0. This is a key-specific harness, not a global type-erased
TLS replacement; timing/test TLS keys are outside it. Its generic pointer
cast must only be instantiated with this exact PROGRAMMED type.

The concrete source obstruction remains insertion/representation, already
reached in the split gate. No universal library contract is available to
instantiate writes_decode. The partial owned sampler integration does not
supply the concrete remaining gamma/ordinary/query policies, circle-caller
reachability, nominal caller carriers, retry/error/serialization assembly
or full native trace identification. The generic history theorem below
does not prove these source equations.

## Endpoint decision and verbatim before/after

`shippedProverExperiment` and both WholeRunJoins remain **unconstructed**.
The insertion obstruction is not repaired by assuming the universal
operation contracts used in the schedule induction. Likewise the generic
joint interpreter law is not an instance of the shipped caller. Removing
or narrowing RustProverRefinement now would hide unproved source obligations.
The owned suffix's QM31 policy is genuinely instantiated, but the deployed
endpoint premise is unchanged. No adversary, randomness carrier, bad event,
query schedule or privacy conclusion is weakened or renamed.

The new single-thread live-key requirement is explicit in the local TLS
contract and the P6/runtime description above. It adds no Lean axiom and
is not smuggled into a supposedly unconditional deployed theorem. The
original and fuel-enlarged endpoints are both audited in the final target.

Before (`cb9372b8f`, ProverCommitDeployedFuel22):

```lean
def RustProverRefinement : Prop :=
  (∀ (adv : rust.Adversary) (w : (h).Instance), (h).public w = x.1 →
    Nonempty (ProverCommitFuelJoin22.RunJoin
      (fun r => let v := rust.real h B outputs adv x w r; (v, rust.observe adv v))
      (fun r => let a := RomObserverBin.observerMap rust observer_program adv
                let v := (source).real h B outputs a x w r
                (v, (source).observe a v))
      (QueryScanRealLazyBound.realBad W Pr 8 h B outputs x w)
      (realSeedQueries template outputs x rust observer_program adv w))) ∧
  (∀ adv : rust.Adversary, Nonempty (ProverCommitFuelJoin22.RunJoin
      (fun r => let v := rust.ideal (simE (h).transport B outputs x) adv x r
                (v, rust.observe adv v))
      (fun r => let a := RomObserverBin.observerMap rust observer_program adv
                let v := (source).ideal (simE (h).transport B outputs x) a x r
                (v, (source).observe a v))
      QueryScanIdealHistory.selectedBad
      (idealSeedQueries template outputs x rust observer_program adv)))

theorem privacy_headline_deployed
    (refinement : RustProverRefinement template outputs x rust observer_program)
 :
    ZK_FSS h B outputs rust x (simE (R0Z.ZkStatement.HonestProver.transport h) B outputs x)
      (modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge) ∧
    modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge ≤
      1 / 2^109 + 1 / 2^137 + 1 / 2^454 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge ∧
    modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge < 1 / 2^100
```

After (this branch; byte-identical):

```lean
def RustProverRefinement : Prop :=
  (∀ (adv : rust.Adversary) (w : (h).Instance), (h).public w = x.1 →
    Nonempty (ProverCommitFuelJoin22.RunJoin
      (fun r => let v := rust.real h B outputs adv x w r; (v, rust.observe adv v))
      (fun r => let a := RomObserverBin.observerMap rust observer_program adv
                let v := (source).real h B outputs a x w r
                (v, (source).observe a v))
      (QueryScanRealLazyBound.realBad W Pr 8 h B outputs x w)
      (realSeedQueries template outputs x rust observer_program adv w))) ∧
  (∀ adv : rust.Adversary, Nonempty (ProverCommitFuelJoin22.RunJoin
      (fun r => let v := rust.ideal (simE (h).transport B outputs x) adv x r
                (v, rust.observe adv v))
      (fun r => let a := RomObserverBin.observerMap rust observer_program adv
                let v := (source).ideal (simE (h).transport B outputs x) a x r
                (v, (source).observe a v))
      QueryScanIdealHistory.selectedBad
      (idealSeedQueries template outputs x rust observer_program adv)))

theorem privacy_headline_deployed
    (refinement : RustProverRefinement template outputs x rust observer_program)
 :
    ZK_FSS h B outputs rust x (simE (R0Z.ZkStatement.HonestProver.transport h) B outputs x)
      (modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge) ∧
    modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge ≤
      1 / 2^109 + 1 / 2^137 + 1 / 2^454 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge ∧
    modelError (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) L₁ L₂ + 16 / (2 : ℚ)^486 + QueryScanFreshUnion.freshBudget (8 * n1 (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) (R1Z.PhaseLocalityBin.R1PhaseProver.toProver (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed)) + 1) + 2 * ProverCommitSeedEvent19.budget (2^64) + 2 * ProverCommitFuelMass22.charge < 1 / 2^100
```

## Final focused verification and handoff

J7486, `R1Z/ProverCommit23Audit.lean`: exit 0, wall 2.37 s,
peak RSS 4088352 KiB, swaps 0, source revision `018cc5197`
plus the exact additive audit source SHA-256 and dependency fingerprint
in `lean/lean-7486.json` and `lean/attempts-7486-7487.jsonl`.
All **24** full #print axioms lines are retained in `lean/out-7486.log`:
20 new top theorems, both deployed endpoints, and the two reused oracle-law
boundaries. Every accepted set is a subset of
[propext, Classical.choice, Quot.sound]. Only one final changed-cone audit
ran. Earlier focused source versions are retained with explicit status;
no unchanged full regression was repeated.

`harness/bind-source.py` reconstructs every Rust attempt's exact cumulative
source delta against the pinned part-22 host base, including the rejected
first TLS signature. It checks the source prefix after exactly the inherited
coin18 projection, and unchanged trace/sampler bodies. The output is
`source-prefix-binding.json`. `harness/final-audit.py` checks all source
snapshots, accepted/excluded receipts, axioms, resource caps, original
endpoint equality, report before/after text and unchanged shipped files;
its output is `final-audit.json`.

No local file under crates/ or programs/ changed. The D129 three-frozen-ELF
evidence is reused for unchanged shipped source; no new ELF equivalence
claim is made. All new Rust instrumentation is host-only and cfg(kani).
No concurrent-owner file, wallet, key or authority changed; no binaries,
objects or archives are committed. No pushes. No SSH session approached
twenty minutes without output. Env J uses the global lock, one Lean job
at a time; no existing other-worker source/object was overwritten. This
job's own new Policy23 object was updated before compiling its final
consumer; all required dependent audits use that updated object.

A complete frozen release replay is withheld because the concrete source
closure is not green. All 7000–7473 receipts were already occupied at start;
this packet consumed **7474–7486**. Next candidate **7487**, within
7487–7499, subject to another receipt check.

The next concrete deliverable is a universal Rust tree insertion/state
representation proof (the two bounded read gates do not suffice), followed
by the concrete source marked-program/Fresh/counter-room instance and
finite coupling marginal construction. Remaining gamma/ordinary/query,
circle caller, native trace, caller carrier and retry/error/serialization
joins must be composed before either WholeRunJoin or an honest narrowing
of the deployed RustProverRefinement. The release target is unchanged
and **not yet established**.
