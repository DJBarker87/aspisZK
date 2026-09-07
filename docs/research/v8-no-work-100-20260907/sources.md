# Primary-source audit, accessed 2026-09-07

## Constructions and decoding

- [ZK IOPPs for Constrained Interleaved Codes](https://eprint.iacr.org/2026/391),
  Chiesa–Fenzi–Weissenberg; received 2026-02-25, approved 02-26. Downloaded PDF
  SHA-256 `6a2092b7bc50e5ea68ec8e679c4b830f2fe260c961dc08ee7582b7e652a46f7c`.
  Read exact Theorems 6.2 (masked sumcheck), 7.1 (base case), 9.10 (code switch)
  and composition Definition 4.3/Theorem 4.5 context. Theorem 6.2 adds a mask
  oracle and non-oracle messages; Theorem 7.1 discloses masked messages and
  randomness and authenticates both main/mask sides. Theorem 9.10 requires
  source, target and mask ZK encodings, zero-evaders, list bounds and mutual
  correlated agreement. Its field/vector-alphabet flexibility is useful, but
  does not instantiate Aspis's heterogeneous adaptive C2 or its query leakage.
  HVZK composition explicitly controls future queries; it is not a finished
  Fiat–Shamir simulator for this application. No small-instance overhead
  percentage was imported. The all-versions web endpoint failed; landing-page
  history and current PDF hash pin the version actually read.

- [VEIL](https://eprint.iacr.org/2026/683), Dalal–Hemo–Rabinovich–Rothblum;
  received April 7, revised April 13 (ZK-code clarification and fully-ZK circuit
  evaluation fix). PDF SHA-256
  `106e33cbc17ba7c9e6523b0eab67b38f0c4f9acfc8516f1a83e807d68f3cc2fa`.
  Read Definitions 2.12–2.13, Lemmas 4.3, 4.7, 4.8 and Figures 7/10.
  The outer circuit-evaluation scheme checks exposed algebraic messages and
  costs extra commitments/openings. Lemma 4.3 sums two binding errors; Lemma
  4.8 needs an appropriate partially-ZK multilinear evaluation scheme. Neither
  supplies Aspis ownership extraction or its exact ROM compiler automatically.
  The 2^29-element benchmark is inapplicable as a percentage estimate for 1,024
  rows. The all-versions endpoint failed; current bytes and stated correction
  were inspected.

- [Plonky3](https://github.com/Plonky3/Plonky3/tree/3da160d09d1c6a878adaa5b339939fcdccda5d36/whir/src/pcs/zk),
  pinned `3da160d09d1c6a878adaa5b339939fcdccda5d36`. Read `mod.rs`,
  `proof.rs`, `security.rs`. Implementation has masked sumchecks, per-switch
  mask commitments, private OOD pads, base-case main/mask fresh commitments,
  blinded messages/randomness, and all associated openings. Its generic code
  requires TwoAdicField; M31's multiplicative group has only one power of two,
  so Aspis circle encoding is not a drop-in implementation of that interface.
  Its diagnostic security report expressly does not certify the compiled PCS
  or preceding reductions and accepts grinding parameters. Zero those credits
  while preserving selection before assessing a candidate. No library build
  or external code execution was needed for this screen.

- [WHIR](https://eprint.iacr.org/2024/1586), revised 2024-11-21; and
  [STIR](https://eprint.iacr.org/2024/390), fourth revision 2025-01-27.
  Landing-page histories and the repository's exact code-switch audit were
  checked. The revised WHIR compiler and STIR protocol/Appendix-B corrections
  are relevant; their large-instance timings are not Solana CU. Full independent
  re-audits of both PDFs were not performed in this bounded screen. The 2026/391
  exact statements and current implementation were the concentrated ZK audit.

- [S-two](https://eprint.iacr.org/2026/532), downloaded hash
  `e3b0132ec598ca16835c1de3c85d0c8b07c41b5f063f1d88b5a9628c22252c3f`,
  identical to the repository pin. Appendix A.2 Theorem 25 gives the
  curve/list factor `L*((2*L^4/3)*(1-delta)+1)*M*N`;
  Remark 26 permits its slightly smaller original term, and Theorems 28/29
  require set-specific/weighted variants. This is already reflected in the
  repository's Hensel/weighted reconstruction. The exact initial/final outer
  budgets 87316067086790/2388155905379 offer roughly two bits, not 25.
  [BCH+25](https://eprint.iacr.org/2025/2055), Lemma 3.1, Sections 3.2/4.1,
  is already incorporated. Formalizing it again supplies no new bits.

- [Locality of Curve-Decoding](https://arxiv.org/abs/2607.08516v1), July 9,
  2026, and [Goyal–Guruswami revised March 24](https://eccc.weizmann.ac.il/report/2025/166/):
  screened statements concern subspace-design/folded codes and random
  evaluation ensembles. They do not certify fixed deployed circle domains.

- Very recent [TR26-169](https://eccc.weizmann.ac.il/report/2026/169/), posted
  September 6; PDF hash
  `b17d9f407a9d9d8ae3ad557c48debb4e2a88534abe5c0cadc4151d41ba49a6c1`.
  Read Theorems 1.1/1.2 and characteristic discussion. It claims prescribed
  prime-field evaluation sets with effective constants C and n0, errors n^C/q,
  and q^C extraction time. QM31 is not a prime field; the finite constants and
  threshold for Aspis are not instantiated. This new preprint has not been
  independently validated here. It is a bounded follow-up lead, not credit in
  the current ledger or a reason to replace the selected code on an abstract.

## Runtime: verified implementation versus feature availability

- The supplied [tweet](https://x.com/deanmlittle/status/2046518488869810505)
  returned 403; searching its exact ID did not recover verified contents.
  No claim here identifies what that tweet says.
- Independently found [SIMD-0512](https://github.com/solana-foundation/solana-improvement-documents/blob/main/proposals/0512-sha512-syscall.md)
  (status still Idea in fetched proposal) and
  [Agave PR 11969](https://github.com/anza-xyz/agave/pull/11969), merged
  2026-04-17, merge `6eb39b55b5724930343d6c4fccef3ec857764ca8`.
  Read patch and tests: SHA-512 uses the SHA-256 base/byte/max-slice parameters,
  validates 64 output bytes, and is gated by `enable_sha512_syscall`.
  Current Agave pin `f50e2ffd906d8b2d702218de236cd419477fb10f` maps the feature
  to `s512oDwgx8hjMnaQjXfqqrZroVj4HvC6TkN3iSSWXCh`.
- Public read-only `getAccountInfo` at finalized commitment: mainnet slot
  444997423 returned null (API 4.2.2); devnet slot 494453696 returned active
  Feature-owned state `AQA+HhwAAAAA`; testnet slot 439470771 returned active
  Feature-owned state `AWDm0xgAAAAA` (both API 4.3.0-beta.3). Thus activation is
  observed on devnet/testnet, not mainnet at these snapshots. RPC responses
  are trusted read-only observations, not a deployment executed by this agent.

Metered cost follows base + per-slice max(memory base, byte cost*floor(len/2))
in the inspected hash implementation, plus program instructions and translations.
SHA compression blocks are not the CU tariff. Parent inputs remain 53 bytes if
digests stay 26 bytes; SHA-256 and SHA-512 each need one padded block there.
Full 64-byte digests make parents 129 bytes (two padded SHA-512 blocks) and add
76*(frontier+1) proof bytes relative to two 26-byte trees. Wider output does not
widen QM31, improve query soundness or permit changing transcript framing freely.
A 64-byte transcript state would also enlarge squeeze/absorb inputs and require
a new sampler/compiler analysis. No SHA-512 CU saving is claimed.

Existing SHA-256 hashing is usable in the matched baseline. SIMD-0449 direct
account pointers and TxV1 are potential data-access/transaction improvements,
but this run did not establish activation or an Aspis CU delta for them.
Host/JIT speed, larger transaction limits and rent do not reduce proof-body bytes.
