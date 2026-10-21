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

The part-20 arbitrary-oracle obstruction remains binding. No artificial
abort or cap is introduced. Pending admitted-input analysis.
