# Canonical oracle queries and C1 recovery

The byte-log recovery result now connects to a literal Merkle program over
the same finite oracle-address type used by the Fiat–Shamir development.
Canonical-address filtering supplies byte-hash consistency as a theorem.
For C1, a prior read of the existing initial-frame encoding also places the
missing-root case in a separately bounded parsed-target event.

This closes a model interface left explicit in
[the recorded-log checkpoint](MERKLE-RECORDED-LOG.md). It does not establish
Rust correspondence, a complete committed-word extractor, or private-spend
security.

## Canonical bytes without discarding adversarial queries

`Addr L` is an option-byte vector. `Addr.toBytes` filters `none` cells, so two
different vectors can yield the same bytes. Their oracle outputs cannot be
assumed equal under the full finite random oracle.

`CanonicalByteAddress.normalize` encodes the extracted bytes with the existing
`Addr.ofBytes`. The roundtrip and idempotence lemmas characterize canonical
addresses. `CanonicalByteHash.encode` agrees with `Addr.ofBytes` on inputs of
length at most `L`; its out-of-range branch merely totalizes the function.
`hashBytes H` is the actual finite oracle `H` applied to that encoding.
The later opening theorem proves all relevant input lengths, so it does not
use the out-of-range branch for an opening.

`CanonicalOracleLog.canonicalTrace` filters the recovery records to canonical
queries. Its `consistent` theorem derives byte-hash consistency from ordinary
oracle consistency of the original trace. If a bounded input is absent from
this recovery log, its canonical address was not read in the original trace.
No assumption that all prover queries are canonical is added. The full
unfiltered trace, and all its distinct reads, remain in every event and budget.

The canonical test, log filter, strict parsers, and finite lookups are
constructive. Their checked declarations do not depend on `Classical.choice`.
The disjunction proofs may use that standard axiom; they do not turn the
unimplemented whole-spend extractor into a constructive algorithm.

## Literal opening program

`CanonicalMerkleProgram.program` renames the already checked byte-input
`MerkleProgram.leafProgram` through the canonical encoder. `eval_program`
reuses the old evaluator-renaming theorem to give its complete trace and
returned digest. `read_of_input` places every literal opening input in that
trace, and `fullTrace_bounded` uses the existing node-shape lemma to bound
every input by `L` from the leaf bound and `257 ≤ L`.

`CanonicalMerkleRecovery.recover_or_events` assumes a consistent prior trace,
the tagged fixed-width leaf and 32-byte salt, the address-size bounds, acceptance
of this literal opening program, and a distinct-read budget on the prior
trace followed by that program. It proves one of:

1. Exact payload/salt recovery from the earlier canonical query records.
2. A cross-trace collision between a prior recorded byte input and an opening input.
3. A fresh opening input hitting the supplied root.
4. The existing parsed-child first-read event on the full unfiltered trace.

It no longer takes a separate byte-hash consistency or opening-read-inclusion
assumption. It does still take the actual prefix, accepted path, and read
budget as inputs.

## Initial C1 specialization

`MerkleC1Target.pred` reuses `PublicInitParse.parse`. Its roundtrip recovers the
supplied C1 digest from the literal P3 initial frame. The singleton-family
adapter reuses `ParsedTargetsCollision.mass` to bound that event by
`Qtot² / 2^256` for its stated full oracle experiment. The previously checked
child-family bound is `8*Qtot² / 2^256`.

`CanonicalC1Recovery.recover_or_events` specializes to tag `0x71`, a 480-byte
packed payload, and a 32-byte salt. It requires a prior read of the exact
initial frame with this public byte string and root. That read fixes the
root predictor before any absent opening input's first read. Applying the
existing prefix-hit theorem covers the fresh-root case. The conclusion is
exact recovery, a cross-trace collision, a child-target event, or the C1
root-target event.

The theorem accepts a prior trace containing that frame. Instantiating it at
the correct commitment-time cut of the actual experiment remains necessary;
mere frame membership in an arbitrary later prefix does not establish that
the reconstructed word was fixed before the protocol challenges.

## Remaining gates

The subsequent [three-commitment checkpoint](THREE-COMMITMENT-RECOVERY.md)
adds the C2 and folded-root frames and lifts cross-trace collisions to the
common finite-oracle collision event. The terminal Merkle program still
must be composed with the actual transcript and checkpoint verifier,
including intervening queries. The source's actual slot indexing, folded-tree
padding, parser/account provenance, and commitment-time prefix selection
also require correspondence.

These results neither supply an efficient list decoder nor discharge the
arbitrary-table D2 knowledge obligation. The full privacy/simulator proof
and security-ledger instantiation remain open. The accompanying
[budget profile](FS-BUDGET-PROFILE.md) preserves the query factor and does
not interpret a per-query coefficient as a complete failure probability.

## Focused evidence

Seven changed components compiled individually on the pinned NUC cache,
followed by `R1CanonicalMerkleCheckpoint` once. The checkpoint exited 0 in
0.74 seconds, used 1,799,100 KiB peak RSS with zero swap, and ran under
4G/6G/zero-swap cgroup limits. All 27 axiom reports contain only `propext`,
`Classical.choice`, and `Quot.sound`; no proof placeholders occur.

Base revision: `a9d4c4bee5e2cf34ac91056b9e9a7a7ab4e1643f`. Checkpoint source:
`0cddd88fc2a7d9fe41ea898897be3722f7c38e46240a7c81e982b0a0cb5692f6`.
The sealed bundle `evidence/lean-canonical-merkle-20261014/` retains all
27 source-snapshotted attempts, including 19 failures, resource receipts,
compiler output, and compiled objects. No runtime source changed.
