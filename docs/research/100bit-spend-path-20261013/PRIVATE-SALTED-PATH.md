# Salted R1 candidate and the remaining ROM argument

> Note (2026-10-19): the R1 proof format is now the compact binary-multiproof format, fixed length 57,607 bytes (`evidence/format-adopt-20261019/REPORT.md`); 124,343 bytes below is the retired eight-way format.

Root design, 2026-10-13. This describes the default-off P3 experiment. It is
not a claim that the current Rust program is zero knowledge.

## Concrete change

Each leaf of each of the three committed oracles gets an independently
domain-separated 32-byte private salt. The initial C1 and C2 tree tags are
0x71 and 0xf1; the intermediate tree tag is 0x72. Hash leaves as
`SHA256(0x10 || tag || fixed-width values || salt32)`, using the repository's
existing private-leaf primitive. Only queried salts are disclosed. There
are still six 8-ary authentication levels. No trusted setup is introduced.

A two-fold proof gains 22*3*32 = 2112 bytes, to 124343 bytes. Uploads remain
outside the user's verification/settlement count. The private salt vector
is host-only: the verifier receives one salt per opened leaf, and uses the
same number of leaf and internal-node hashes as before. Actual CU cost, including the larger proof digest and lifecycle operations,
has now been measured in the real Pool adapter under LiteSVM; all six
fresh-OS-mask transfer/withdrawal cases fit two 1.4M-CU transactions. See
`evidence/p3-private-leaf-salts-20261013/`.

P3 has separate proof magic, semantic and opening transcript domains, and
Pool registry profile/release bindings. An unsalted proof must not be
accepted under the salted profile. The arithmetic field choices, 22-query
count, D18 transport and proposed decoder/root-count ledger are unchanged.

The honest host path reuses `StateOnlyAttemptSecrets` and
`DurableStateOnlyMaskNonceStore`. Reserve the unique public attempt nonce
before mask or salt derivation. Use independent OS-generated field-mask
entropy and leaf-salt seed; hash their domain-separated expansion only
through the approved reserved-attempt context. A failed attempt keeps its
nonce reservation. Test fixtures remain explicitly deterministic and unsafe
for live use. A fresh entropy API alone does not establish zero knowledge.

## Why salts help, and what they do not prove

Unopened unsalted leaves require a proof that their values retain sufficient
conditional min-entropy after the complete disclosed algebraic transcript.
Private independent salts give a direct hidden-input route for the Merkle
commitment simulator. This separates commitment hiding from the linear mask
image argument. It does not make the exposed algebraic values private by
itself, nor does it establish an efficient full transcript simulator.

The intended proof sequence is:

1. For fixed public challenges and query positions satisfying the explicit
   rank predicate, prove the normalized disclosed algebraic payload is the
   publicly computable mask-map law. The two-pad construction and pure-chain
   repair in `PRIVACY-RANK-PATH.md` are the proposed route. Show offset
   membership against a public reference, not merely pairwise witness
   independence. This provides an efficient algebraic simulator.
2. Simulate consistent opened leaves and authentication paths with random
   salts and hashes, programming the commitment oracle where necessary.
   Repeated openings of the same intermediate leaf must share the same
   values, salt and path; independent per-query sampling would be wrong.
3. Program the domain-separated FS transcript consistently with those
   commitments and public algebraic values. Charge pre-existing input hits,
   digest collisions, and all seed-expansion/commitment/transcript oracle
   domain interactions under an explicit query-count ledger.
4. If the honest prover rejects deficient rank predicates, simulate the
   same bounded attempt/abort process. The predicate must depend only on the
   public statement and challenges/queries, and be checked before any
   upload. Account for observable retry behavior; do not condition away a
   witness-dependent abort event without proof.
5. Prove the source correspondence for the actual P3 byte grammar, reserved
   seed expansion, masks, transcript order and publication boundary.

In the ideal independent-tape model, the accepted good-rank algebraic law
would be exact. In the implemented 256-bit seed expansion it is an oracle
hybrid, not statistical independence of an arbitrarily long tape. The
reduction must include that distinction. A bound on rank rejection is
needed for standard completeness and expected proving time; sampled passing
ranks do not supply a universal density theorem.

This plan deliberately leaves the random-oracle security loss symbolic
until its events and query domains are proved. The proposed soundness
coefficient of about 2^-105.136 is a separate ledger; it is not automatically
a bound on zero-knowledge distinguishing advantage.
