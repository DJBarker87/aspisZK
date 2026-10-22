# Proof-account route L1 closure — 2026-10-22

Status: partial model/control handoff; native L1 target not yet established.

Scope: D162 public proof-account nonce → `generate_for_mask_nonce` →
`prove_masked_retrying_with`, S2, native prover/r1p-check/private-leaf-salts.
The current frozen source retains TLS instrumentation. L1 includes its counts
and bytes; duration magnitudes remain L3. No shipped source changes.

## Stages

1. Define an ordered L1 record, with retained TLS state and exact error origins.
2. Prove retry ownership and conditional hazard identities without iid premises.
3. Audit the joint coupling interface and numerical charge; close only if the
actual source observations are covered.

## Trust and release boundaries

Retain E1, E2, P1, existing source refinement and TrustedStd/TLS boundaries.
No deployment binary/CPU pin is supplied by this proof-only task. D162 selects
a route; it does not certify a checked-in caller. No keys are created or removed.

Receipts: `docs/research/100bit-spend-path-20261013/evidence/sidechannel-l1-20261022/`.

## Stage 1 — record and retry-owner erasure

`R1Z/SideChannelL1AttemptRecord.lean` defines the ordered event carrier,
precise call/detail plus API error label, retained TLS bytes/check count,
attempt prefixes and returned count. It distinguishes callback Rejected
(abort) from attempt Rejected (retry). Partial underlying writes and errors
are represented individually, including interrupted writes; this is richer
than the previous logical-write environment model. Ledger contents/path
observations are public nonce/statement data, never private seed bytes.

J9865 passes: nine audited theorems, standard axioms only, wall 2.07s,
peak RSS 4,191,300 KiB, swaps 0. J9864 failed on an omitted list-length
simplification, fixed before rerun. J9800 was refused before compilation:
historical J9800–9863 receipts already existed. Only unused IDs are used.

Established: richer reference erases exactly to part-34 retry control,
retaining all state, with rejected/stopping/success prefixes and cap eight;
TLS append/count/retention semantics. **Not established:** every native
callee emits the declared record, honest-domain constant guards, or joint
privacy of this record. `source-map.json` is a manual source map, not a
source-refinement proof. It does not discharge those obligations.

## Stage 2 — conditional retry identities

`R1Z/SideChannelRetryLaw.lean` proves the rejection-prefix characterization,
callback-stop rule, cap-exhaustion execution and the audit's conditional
success/abort/entry identities for every `k : Fin 8` (human attempt k+1).
The finite carrier can retain the entire ROM, policy, ledger and seed tape;
no independence or stationarity premise is added. History-conditioned
identities and arbitrary failure-origin predicates use the same conditional
mass. Zero-mass prefixes are handled without excluding them.

J9867 passes: ten audited theorems, standard axioms, wall 1.79s,
peak RSS 4,169,768 KiB, swaps 0. J9866 failed because `prefix` is a Lean
syntax keyword; renamed the binder. The identities are exact for this
instrumented terminating reference. They do not supply any numerical
acceptance hazard or discharge native callee/event refinement.

## Stage 3 — two-seed counts and history

`SideChannelEntropy.generate_lift` proves that every permutation of successful
nonzero seed pairs preserves the complete entropy prefix state, including RNG
statuses/count, cursor and ledger additions, for **every** byte-blind schedule.
Rejected raw candidates stay fixed. `generate_count_cap` bounds the number
of appended RNG history entries by sixteen. These use the exact two-block
model from `ProverCommitOwnerModel42.generate_model`; the existing part-42
bridge supplies source-owner correspondence, with its retained P6 boundary.

`SideChannelEntropyLaw` proves by symbolic coordinate products that, under
uniform independent raw draws and the all-Ok schedule, u=2^-256 gives:

- rejected candidate mass r=2u-u²;
- first acceptance at n+1 has mass r^n(1-r);
- sixteen-candidate exhaustion has mass r^16.

The first-acceptance theorem is an ideal finite raw-tape calculation; it is
not a numerical geometric law for outer prover retries. General faults use
the exact conditional hazards from stage 2. Entropy state equivariance is
proved jointly, while composition with the later masked transcript remains
open.

J9869 and J9872 pass, standard axioms; walls 2.04s/2.13s, peak RSS
4,162,908/4,174,032 KiB, swaps 0. J9868 failed on an ambiguous helper and a
missing match simplification. J9870 reached the Lean memory limit (peak
7,168,988 KiB, exit 1) in concrete `bad_exact`; it was **not** rerun unchanged
or with a larger cap. Replaced it with generic `pair_bad_exact`, then applied
the existing answer-cardinality theorem symbolically. J9871 exposed one
rational normalization step, fixed in J9872. Raw logs retain all failures.

## Stage 4 — joint TV tools, numerical candidate and the open source join

`SideChannelL1JointCoupling.dist_le_bad` proves the actual finite rational
TV inequality on arbitrary observation types. `joint_union_bound` charges
each member of a named bad-event family once. These are generic mathematical
tools: their agreement and per-event bounds have **not** been instantiated
for a complete native L1 record.

The retained part-40 numerical envelope is below 2^-100. The explicit
worst-budget two-witness *candidate*, obtained by doubling that envelope,
also satisfies the target:

```
2 * (2^-109 + 2^-137 + 2^-454 + 2^-118 + 2*2^-192
     + 48/(2147483647)^5 + 2^-183 + 48*2^-256) < 2^-100.
```

This is `two_witness_candidate_numeric`, not a native TV theorem. The
terms come from the retained model/pole, query, seed, mask-fuel, private-memo
and entropy allowances. Their native joint event assignment remains open;
they must not be added again as separate L1 penalties. No bound or exact
excess for the complete native L1 law has been established here.

The module also gives a concrete two-bit countermodel to a **proof
inference**: a public bit `w xor coin` has identical laws for both witnesses,
and count `if coin then 1 else 2` is witness-independent. Observing them
jointly reveals w with certainty. This is proved in Lean, including test
masses 1 and 0. It is not a valid-spend pair, a SHA preimage, or evidence that
the actual TLS implementation leaks in this way. No actual TLS witness leak
or full valid-spend counterexample was found; no TLS field was dropped.

J9876 passes (wall 2.01s, peak 4,172,976 KiB, swaps 0). J9873 failed only on
ambiguous `dist`; J9874 passed before the final numerical addition. J9875
then connected prefix events to the actual returned record-list positions:
`actual_entry_iff` and `actual_entry_mass` characterize all eight entered
iterations, and all-rejected control really reaches cap exhaustion. J9877
adds explicit RNG-status/count, checker-call, failure-origin and return-count
projections. J9878 rebuilds its retry-law dependent. These focused source/
dependency changes are the reasons for the reruns.

### Existing public machinery reused and its limits

- Parts 39–40: `ProverCommitPublicNonce40.public_reservation` applies the
  exact shared-ledger coupling, for unrestricted public nonce and arbitrary
  finite retained ledger. Public binding/address memo hits are not rare
  events and have no new reservation-guess penalty.
- Part 42: the two-private-block owner/model equality is the entropy
  source boundary used above. `ProverCommitGlobalRun42.continuation` transports
  an arbitrary observer of the normalized read vector **for one witness**.
  It does not prove equality of two witnesses' full L1 histories.
- Part 46: `ProverCommitFinalize46.finish_decode` and
  `programming_publication` preserve proof/table/flag finalization. Neither
  statement supplies a full native L1 event producer. D160's source-view
  byte-image work remains with part 47; its files were not edited.

### What prevents the requested closure

Priority 1 is only partly closed: the richer event grammar/reference and
retry control are checked, but native per-callee event refinement is missing.
Priority 2 (the concrete joint coupling) is open. In particular:

1. Construct the native L1 producer and prove its event/refinement equation,
   including partial `write_all` operations, exact error origins, honest
   guard invariants, post-gamma allocation/error prefixes, CHECK_TIMES pushes
   and full ordered trace bytes. An arbitrary `Owner` is not that theorem.
2. Extend the witness-mask transport to **jointly** preserve successful mask
   values, rejection/refill counts, retained ROM/ledger state and every
   rejected-attempt TLS prefix. Entropy-prefix symmetry is not sufficient for
   the later masked transcript. Do not infer this from marginal hiding.
3. Install the equal-circle and query-exhaustion abort branches and their
   TLS/checker prefixes in the same source coupling. If shared challenge
   blocks couple these events exactly, prove it there; if a new bad event is
   needed, provide its conditional bound and charge it once. No new rare-event
   allowance is assumed here.
4. Join part 47's native byte image to the published proof/oracle view and
   the complete L1 record, then perform the FS conversion. Initial TLS values
   must be retained/conditioned as prior observable history, alongside the ROM
   and ledger, rather than reset at the start of each proof.

These are missing proofs, not new cryptographic or runtime trust items.
No `FullRecordAgreement`/similar premise has been installed to relabel the
requested conclusion as an assumption. The generic TV theorem is deliberately
not advertised as the requested concrete `SideChannelL1JointCoupling` result.
