# Proof-size proposal (external calculation, 2026-10-19)

> Note (2026-10-19): the R1 proof format is now the compact binary-multiproof format, fixed length 57,607 bytes (`../evidence/format-adopt-20261019/REPORT.md`); 124,343 bytes below is the retired eight-way format.

Supplied by the user from an outside analysis of `research` at 9d12464c. It
is a structural calculation, not a measurement; nothing in it has been
implemented or benchmarked. It is the input to
`PREREG-PROOF-SIZE-20261019.md`.

## Summary of the proposal

The salted S2 proof is 124,343 bytes: Merkle authentication paths 88,704
(22 queries × 3 trees × 6 levels × 7 siblings × 32 bytes), opened values and
salts 18,304, semantic proof/final coefficients/roots/framing 17,335.

1. Compact QM31 encoding: 455 values are stored as 32-byte WideExact with
   the upper 16 bytes required to be zero (semantic records and the 29 `y1`
   values). Transmit 16-byte canonical encodings; rebuild the logical record
   with its zero halves when hashing, so Fiat–Shamir messages are unchanged.
   Saving 7,280 bytes → about 117,063.
2. Eight-way Merkle multiproofs (one per tree per transaction batch, 10/12
   queries) keep the roots and leaf hashing; with compact encoding about
   94,983 bytes. Not sufficient for 60 KB.
3. Binary trees with one multiproof per tree per transaction batch: a
   conservative maximum of 914 supplied sibling hashes (C1 318, C2 318,
   folded 278, the folded tree's openings lying in the first 2^16 positions of
   the padded 2^18-leaf tree, padding still authenticated), so authentication
   ≤ 29,248 bytes and the proposed total ≤ 57,607 bytes before small framing.
   Roots and therefore Fiat–Shamir challenges change.
4. Hash-syscall budget under Agave 4.2.1 (85 + max(10, len/2) per slice):
   extra binary parent hashes about +35,400 CU (up to 974 binary parents vs
   396 eight-way), hashing a 57.6 KB proof twice instead of 124.3 KB about
   −66,700 CU; net about −31,300 CU. Syscall charges only; SBF instructions,
   sorting/indexing, frontier management, decoding and allocation are not
   included. The checkpoint must authenticate the compact stored bytes.
5. Proof obligations: for compact fields and same-tree multiproofs, a
   representation/refinement theorem (compact verification ⇒ the same
   authenticated values and checks as the reference) with strict decoding,
   index ordering, complete consumption, duplicate folded-leaf handling. For
   binary trees, a contained commitment-layer revision: binary commitment
   binding and indexed multiproof verification, the extractor's
   commitment-word recovery, root and transcript serialization, oracle-read
   counts and the privacy simulator's commitment layout.
6. Not proposed: fewer queries, removed salts, narrowed genuine WideExact
   values, truncated hashes, general-purpose compression.
