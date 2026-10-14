# Finite-table Merkle recovery

The new recovery model gives a constructive finite-list walk and proves
the exact ways it can disagree with a later authenticated opening. This
advances the committed-word boundary. It does not yet supply a parser from
the actual oracle table, a causal commitment theorem, or a spend extractor.

## Recovering a digest and its leaf

`MerkleTable.lookup` scans recorded `(children, digest)` entries and returns
the first matching digest. `walk` traverses a complete slot sequence from
the root toward the leaf. The underlying equality checks all 32 digest
bytes through a constructive `DecidableEq`; lookup and walk do not use
`Classical.choose` or a noncomputable equality instance.

The target list contains the claimed root and the eight child digests of
every recorded node. Its length is proved to be `1 + 8*nodes.length`.
Every digest returned by the walk belongs to that fixed target list.

`MerkleRecovery.recover_or_bad` takes a node table whose recorded outputs
agree with a hash function and a path authenticating a leaf digest. It
proves one of three outcomes:

1. The finite-table walk returns that digest.
2. Two distinct inputs, one recorded and one in the path, have the same hash.
3. A path input hashes to a target in the fixed root/child list, but no
   recorded node has that output.

`MerkleLeafRecovery.recover_or_bad` then looks up a packed leaf and salt.
It adds the analogous missing-leaf outcome, or returns exactly the opened
payload and salt. The fixed packed-width premise is retained; equal
concatenations cannot be split arbitrarily. The collision alternative uses
the combined recorded-node/leaf inputs and the complete literal opening
trace. The theorem does not assume that every preimage is already present.

The missing-preimage outcomes are deliberate. A root can be claimed before
its preimage has been queried. Comparing two existing openings alone does
not rule out later finding that preimage. To charge this event, the table
must be tied to an actual earlier oracle prefix, and the target digest must
be shown fixed before the offending fresh answer.

## Connecting hashes to oracle programs

`MerkleProgram.pathProgram` and `leafProgram` express the actual order of
the literal model's hash queries as `Program` values. Their evaluation
theorems give the full input/answer trace and final root, exactly. This
connects the deterministic path model to the existing oracle interpreter.
It is still a model over byte lists; an embedding into the bounded `Addr L`
space used by the unified transcript and the Rust seven-sibling traversal
remain to be proved.

`ParsedTargetsCollision` reuses the existing causal first-read theorem for
a family of B target parsers. Each parser may read a target from the
current input or an input already in the table. The proved experiment
bound is `B*Qtot^2/2^256`, including the case B=0. B is symbolic. No R1
node/root parser family has been instantiated, and no containment theorem
yet connects the recovery model's missing-preimage events to this event.
It would be incorrect to insert this term into the final ledger before
those connections are established. The ordinary collision term must also
remain accounted for.

## Candidate extraction from partial lanes

`PartialJointList` shows that a response can be projected to any selected
lanes by replacing the others with zero messages and zero received words.
The selected common-agreement support equals the full joint support of
that padded instance. The old 100-candidate bound therefore also applies
to partial tuples, provided unused coordinates are zero and at least
38,230 positions match on every selected lane.

This is useful for a decoder that merges lane candidates incrementally:
there need never be more than 100 retained partial tuples satisfying that
support threshold. The theorem does not implement such a decoder or
produce the per-lane candidates efficiently. The existing noncomputable
GS specification and the wallet-witness extraction boundary remain as
described in [the knowledge audit](KNOWLEDGE-AND-ORACLE-BOUNDARY.md).

## Next proof boundary

Construct node and leaf records by parsing a finite first-read prefix.
Prove the parsers' round trips, record consistency, packed widths, and
completeness for every correctly encoded preimage in that prefix. Identify
roots and child targets with the concrete target parsers. Then prove that
a missing recovered preimage implies a later fresh query hitting one of
those earlier targets, with all queries in the common experiment trace.
This will turn the current deterministic disjunction into a commitment-time
word-binding statement. Mapping those bytes to canonical field words and
supplying the efficient candidate decoder remain subsequent obligations.

## Verification

All seven changed modules passed focused NUC checks under the existing
4G/6G/zero-swap scope. The node recovery target was rebuilt once after the
node-table dependency changed from classical to constructive digest
equality; its source itself was unchanged. The combined checkpoint and
exact receipts are in [the evidence bundle](evidence/lean-merkle-recovery-20261014/README.md).

The new `tools/compile-snapshot.sh` wrapper preserves the source before
calling the unchanged capped runner and refuses to overwrite a previous
snapshot. This makes retention automatic for failures as well as successes.
