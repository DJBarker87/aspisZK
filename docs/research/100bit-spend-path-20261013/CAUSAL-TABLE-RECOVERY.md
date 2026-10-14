# Recovery from the table at the first commitment read

The recovery model now connects the ordered query log to the functional
oracle table used by the existing extractor interface. For consistent
logged representations of the same table, recovery returns the same result
outside the existing full-trace collision event. The result covers both
successful leaves and missing entries, regardless of record order or
duplicate reads.

For each literal C1, C2, and folded-root frame, the new theorem starts with
its presence in the full trace. It selects the **first** occurrence and
equates recovery from a representation of `tableBefore` there with recovery
from the full trace. The caller no longer selects an arbitrary purported
commitment prefix. This remains a theorem about the canonical oracle model;
the Rust terminal decision and byte-to-field parsing are not instantiated.

## The representation argument

`TraceTable.replay` applies the existing table update function to a finite
log. `TraceTableMembership.mem_iff_replay_some` proves that, for a consistent
log, a recorded `(address, answer)` is present exactly when replay returns
that answer at the address. Equal represented tables therefore give equal
record membership. `CanonicalLogMembership` transfers this equality through
canonical-address filtering and byte conversion.

Membership alone is not enough for an arbitrary first-match reverse lookup:
two different preimages of the same digest could make the list order matter.
`CanonicalLogSeparation.separated` rules that out using the already proved
`FS2.Duplex.noColl_injective`, canonical input bounds, and the fact that
the relevant reads appear in the full trace. It does not add a new hash
injectivity assumption to the top-level recovery theorem.

The node and leaf record lemmas then derive uniqueness by digest from exact
parser soundness. `MerkleLogExt.recover_eq` composes the node walk and leaf
lookup equalities. `CanonicalTableRecovery.recover_eq_of_replay_eq` derives
its separation premise from the full-trace event exclusion. Both represented
logs must be consistent with the same oracle; the theorem does not permit
arbitrary corrupt table representations.

## First-read cuts and the three roots

`FirstReadCut.first_read_cut` constructs a prefix, the first matching read,
and a suffix from address membership. Its prefix excludes the address.
`TraceTable.tableBefore_cut` identifies replay of that prefix with the
existing `tableBefore` definition without any hash assumption.

The three full-trace word equalities are:

- `C1TableStability.c1_table_word_of_read` for tag `0x71`, width 480;
- `LaterTableStability.c2_table_word_of_read` for tag `0xf1`, width 128;
- `LaterTableStability.folded_table_word_of_read` for tag `0x72`, width 128.

They retain the full-trace consistency and distinct-read bound, the three
specified event exclusions, input length bounds, and an explicit consistent
finite representation of the relevant `tableBefore`. The previous
[causal commitment proof](CAUSAL-COMMITMENT-STABILITY.md) supplies equality
between recovery before the frame and recovery after every later query.
No new probability term is introduced.

## C1 candidate list and reuse

`C1PartialCandidates` selects lanes 0–25 and 28, zero-padding only lanes 26
and 27. It invokes the existing joint-list theorem to bound its mathematical
candidate list by 100. Equality on those selected words makes the candidate
sets equal; a full candidate projects into this list by the already proved
`PartialJointList.projected_response_mem_lambda`.

This is the current C1 layout: each of four slots contains 26 M31 values
and **one** QM31 value, totalling 480 bytes. C2 has two QM31 values per slot,
totalling 128 bytes. The older 403-byte compact C1 format is different.
The new candidate-list module does not decode either byte format.

The reuse audit also found an exact existing leaf-lookup existence lemma.
The draft duplicate was removed in favor of
`MerkleRecordedLog.lookupLeaf_exists`; only the changed module and its
dependent bridge were refreshed. The frozen decoder, semantic, and runtime
regressions were not rerun.

Detailed inventories record the
[existing causal proofs](../CAUSAL-LEAN-REUSE-INVENTORY.md),
[C1 list interfaces](../C1-PARTIAL-LIST-REUSE.md), and
[table/log boundary before this change](../TABLE-LOG-REUSE-INVENTORY.md).
These are dated source inventories; this checkpoint supplies some of their
previously missing table/log links.

## Remaining work

A consistent sparse log representing the table is still an explicit input.
The theorem does not implement enumeration of an arbitrary functional table
or an efficient witness extractor. It also does not equate bytes with the
typed field words used by the semantic and opening arguments.

The old `FS2.D2` remains quantified over arbitrary unrelated tables; the new
result does not make that premise true for a naive availability classifier.
The concrete causal classifier, its local bounds and accepted-proof
containment, the efficient decoder refinement, source correspondence, and
privacy remain open. The [existing GRS conversion](GS-DECODER-REUSE-PATH.md)
provides a route for the decoder algorithm without inventing a new code.

## Evidence

Base revision: `e21211727fc6ad53a2ef014d3fa3dda72037cef0`. Fourteen focused
components and one final checkpoint are archived in
`evidence/lean-causal-table-20261014/`. The checkpoint ran once after the
components were green: exit 0, 1.29 seconds, 3,134,416 KiB peak RSS, zero
swap, limits 4G/6G/zero-swap. Its source SHA-256 is
`66c30f1d5888ac0f6f122d6e724f376664acc943f6833afe142717e08e791ea9`.
All thirty checkpoint audits use only `propext`, `Classical.choice`, and
`Quot.sound`.

The bundle preserves 39 receipt-backed attempts: 21 failed, three superseded
green, and fifteen final. A zero-byte pre-snapshot staging artifact is
recorded separately and is not counted as compilation evidence. Root
reviewed the final statements and proofs and independently verified sources,
objects, resource logs, axiom output, runner hashes, and unchanged runtime
fingerprints.
