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

No universal std::BTreeMap-to-entry theorem is claimed. A symbolic prefix
summary alone cannot discharge the source-library representation invariant.

## Stage 2 — later simulator traversal

Pending extraction and source identification.

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
