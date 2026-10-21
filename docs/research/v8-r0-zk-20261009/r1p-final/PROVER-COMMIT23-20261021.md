# Prover commitment part 23

Base `cb9372b8f`; branch `codex/cx-prover-commit23-20261021`.

Target not yet established. Work in progress; no source-to-model closure is claimed.

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
