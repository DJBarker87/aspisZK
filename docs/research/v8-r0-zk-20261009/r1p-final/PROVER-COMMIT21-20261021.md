# Prover commitment part 21

Base `ec5946193`; branch `codex/cx-prover-commit21-20261021`.

Target not yet established. Work in progress; every accepted claim below is
limited to the named source/model boundary. No shipped source edits, no
concurrent-owner edits, no pushes.

## Stage 1 — single insertion and table composition

The verified four-byte key-comparison contract (`table-key-v1`) passes
(exit 0, 1.569 s, 295956 KiB). The single owned entry with an arbitrary
first-hit prefix/suffix summary (`table-entry-v1`) passes using that verified
stub (exit 0, 2.914 s, 427616 KiB). Both use unwinding assertions, swaps 0,
6G/8G/no-swap/64-task caps. The Rust gate is an owned source-shaped branch;
it does **not** execute arbitrary std::BTreeMap insertion or arbitrary-length
key comparison. Its summaries are justified only for the abstract entry
representation, not the shipped library representation.

`ProverCommitTablePrefix21` proves `lookup_append`, `insert_append_miss`,
`overwrite_after_prefix`, and `entry_collision` by induction on an arbitrary
finite prefix. The overwrite theorem preserves the prefix and suffix
verbatim and gives the exact sticky flag. It composes with part-20 writes
and adaptive history theorems, without a key-uniqueness or size assumption.
J8733/J8734 are excluded syntax/elaboration failures; changed-source J8735
passes (exit 0, 1.34 s, 2516444 KiB, swaps 0; standard axioms only). Exact
snapshots and dependency fingerprints are in `lean/attempts-8733-8736.jsonl`.

`ProverCommitKeyCompare21.vec_eq` proves arbitrary-length Aeneas byte-Vec
comparison equals List equality (J8739, exit 0, 1.23 s, 2522828 KiB;
J8738 excluded). `ProverCommitTableKeys21.extracted_keys` installs it
through the **actual extracted owned insertion loop** for arbitrary finite
table lengths, preserving indexing/update/growth errors and array value
comparison (J8742, exit 0, 1.28 s, 2530436 KiB). All standard axioms,
zero swap. This is a universal owned-source helper theorem, not the
std::BTreeMap representation proof.

A changed actual `ProgramOne` overwrite-flag gate eliminates key allocation
and comparison by using the empty key, retaining arbitrary 32-byte old/new
answers and an arbitrary initial flag. It still reaches the MemoryHigh
region and is stopped for shape review (exit 1, 90.620 s, 6378692 KiB,
swaps 0). This is excluded, not a counterexample or a passed source gate.
No unchanged larger-cap retry occurs.

No universal std::BTreeMap-to-entry theorem is claimed. A symbolic prefix
summary alone cannot discharge the source-library representation invariant.

## Stage 2 — later simulator traversal

The first suffix extraction isolates the next failure to native TLS tracing:
Charon v1 emits an opaque CircleRow discriminant and is excluded; adding
the enum declaration produces error-free LLBC, but Aeneas v2 fails in
`std::thread::local::LocalKey::with` (exit 2, 2.144 s, 374528 KiB).
An owned byte-trace version translates but exposes external iterator, field
serialization and query-sampler templates. Those templates are retained
as inert `.lean.txt`, never imported or accepted as axioms.

The accepted **generic control** reference moves native trace entries to a
returned Vec of field values and gives gamma, ordinary, qm31 and q22
selection as explicit policy parameters. It preserves all eager squeeze /
advance calls, row labels, payloads and query rejection; it adds no hash
or sampler equation. The concrete policy functions are not proved by this
reference. Circle rows 25/26 remain outside this accepted suffix.

`sim-tail-control-v2` translates with no external templates (Charon exit 0,
32.303 s, 577028 KiB; Aeneas exit 0, 3.281 s, 489104 KiB). Types J8740
and Funs J8741 compile (1.38 s / 2539196 KiB and 5.88 s / 2782816 KiB).
Port changes are only narrowed imports and declaration-order discriminant
expansions, with exact raw/promoted hashes and diffs in `extraction/control21`.
Generated resource settings are unchanged.

`ProverCommitTail21.tail_schedule` decomposes the extracted reference into
rows 27–30 followed by query/rho continuation. `query_failure` retains the
post-query state and previous trace and omits rho. `query_success` retains
the final row-32 state and trace. `semantic_continuation` transports the
accepted 25-row finite source equation through every continuation consuming
its entire result, including errors/state. It does not instantiate the
missing circle/source-carrier/policy/TLS join. J8746 passes (exit 0, 1.32 s,
2531256 KiB, swaps 0; all standard axioms). J8743 passed an earlier focused
version; J8744/J8745 are excluded schedule elaboration failures.

Two optimized differential fixtures instantiate the policy with the actual
source samplers and compare the original `walk` against the part-20 owned
25-row cone, actual circle methods, and the new generic suffix. Both the
success and all-zero/query-rejection paths agree on returned result, the
**entire ordered request/answer history**, and the serialized native trace.
The rejection path retains four scalar trace entries; success has 27.
`tail-runtime-v1` passes (exit 0, 5.171 s, 357184 KiB, swaps 0), under
6G/8G/no-swap/64 tasks. These are fixtures, not universal source refinement.

## Stage 3 — nonzero loop and endpoint

`ProverCommitNonzeroStream21` strengthens the part-20 obstruction: a single
consistent callback can answer zero on every target-stream address while
retaining every answer on every other stream, for all seeds, attempts,
counters and counter wraparound. `frame_stream`, `target_answer`,
`other_answer`, `target_zero_prefix` pass J8737 (exit 0, 2.10 s,
4042696 KiB, swaps 0; standard axioms). J8736 is an excluded simp failure.

Thus finite *protocol dimensions* alone do not imply a uniform bound for
the generic coin callback. The transcript and root streams can be held
fixed while tape-stream nonzero search consumes any finite fuel without
success. This result does not instantiate an accepted P_R1 challenge draw,
does not identify concrete HOST_HASH with the generic callback, and does
not assign a probability to this behavior. Those qualifications matter: it
is not a proof that an actual admitted source run diverges, nor an attack.

No artificial abort, cap, new bad event or total experiment is introduced.
To construct the requested shipped experiment still requires either a
concrete hash termination argument, or a source-faithful treatment of
divergence and its probability/coupling, followed by both WholeRunJoins.
