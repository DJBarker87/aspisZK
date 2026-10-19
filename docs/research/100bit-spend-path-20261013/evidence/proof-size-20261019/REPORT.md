# Proof-size feasibility test (2026-10-19)

Pre-registration: `design/PREREG-PROOF-SIZE-20261019.md` (criteria unchanged).
Proposal under test: `design/PROOF-SIZE-PROPOSAL-20261019.md`.
Base: `research` at 20e596416. Branch `codex/r1-proof-size-20261019`.
Host work dir: `/home/dombarker/project-offloads/codex-r1-proof-size-20261019`.

## Verdict

(pending)

## Plan and time estimate (written before S1)

- S1 size: host tool over the six saved fixtures (re-derive each fixture's 22
  queries from its proof with the shipped transcript code), count multiproof
  nodes for the eight-way and binary layouts, encode the compact and
  eight-way-multiproof layouts for real and verify them against the roots.
  Time: one native release build of the cost-probe crate (~5-10 min) and
  seconds of running. About 1.5 h of writing.
- S2 prototype: host-only; time goes into writing the binary tree,
  multiproof, compact codec, candidate prover output and candidate
  verifier (~3-4 h), then native proving of six fixtures (each a 2^18-leaf
  commitment build, seconds to a minute each).
- S3 SBF + CU: candidate adapter route, driver changes for a variable-length
  proof, two SBF builds and six replays. Estimated separately before S3.
- S4 obligations: source reading only.

## 1. Size (measurement 1)

Tool: `crates/aspis-r1-cost-probe/examples/proof_size_s1.rs` (feature
`compact-binary`, new modules `src/multiproof.rs`, `src/compact.rs`). For each
saved fixture (`aspis-r1-rollover-measurement-20261019/fixtures/*`) it first
runs the shipped `tx1`(split 10)/`tx2` natively (all six accept), re-derives
the 22 queries with the shipped transcript (`Prepared::new`), then:

- **compact only**: encodes the 455 implied-zero-high values (426 in semantic
  rows 14..26, 29 `y1`) as 16 bytes, keeps everything else, and decodes back
  to the shipped bytes (round trip asserted byte-equal);
- **eight-way multiproofs + compact**: builds one multiproof per tree per
  batch (queries 0..10, 10..22) from the nodes in the shipped paths and
  verifies each against the shipped C1, C2 and folded roots;
- **binary multiproofs + compact**: counts binary nodes on the same index
  sets; the encoder/verifier walk is exercised on a synthetic 2^18-leaf binary
  tree for each set (node counts depend on the indices only; the real trees
  are S2).

Verified against the proposal: the shipped proof is 124,343 bytes (16 header
+ 13,831 semantic + 928 y1 + 32 + 224 + 32 + 224 + 2,048 + 22 x 4,864). The
455 count is right (row 14: 1, rows 15..24: 280, row 25: 116, row 26: 29, y1:
29), so compact saves 7,280 bytes. The proposal's 914-node and 2,082-node
worst cases are reproduced exactly.

Bytes before any multiproof node in both multiproof layouts: 28,359
(header 16, compact semantic 7,015, compact y1 464, inactive/round0/folded
root/round1/final 2,560, 22 openings x 832).

| Fixture | Shipped | Compact only | 8-way MP + compact (nodes) | Binary MP + compact, variable (nodes) | Binary, padded fixed length |
|---|---:|---:|---:|---:|---:|
| transfer-13 | 124,343 | 117,063 | 90,503 (1,942) | 55,687 (854) | **57,607** |
| transfer-255 | 124,343 | 117,063 | 91,175 (1,963) | 56,071 (866) | **57,607** |
| transfer-1023 | 124,343 | 117,063 | 91,847 (1,984) | 56,551 (881) | **57,607** |
| withdrawal-13 | 124,343 | 117,063 | 87,815 (1,858) | 54,919 (830) | **57,607** |
| withdrawal-255 | 124,343 | 117,063 | 91,175 (1,963) | 56,071 (866) | **57,607** |
| withdrawal-1023 | 124,343 | 117,063 | 91,847 (1,984) | 56,455 (878) | **57,607** |
| worst case (bound) | 124,343 | 117,063 | 94,983 (2,082) | 57,607 (914) | **57,607** |

No fixture has two queries sharing a folded leaf (u/4). Per-batch node counts
are in `sizes.json`.

**Primary result (lead ruling 2026-10-19: fixed length).** The candidate is
built fixed-length: six node slots (C1/C2/folded for batch A, then batch B)
each padded with zero bytes to its worst-case count [146, 146, 128, 172, 172,
150] = 914 nodes. The stored proof is always **57,607 bytes <= 60,000**
(slack 2,393). The variable-length figures are secondary.

**Worst-case argument.** In one multiproof over a strictly increasing set of
n_0 leaves in a tree of L levels and arity w, let n_l be the number of
occupied (ancestor) nodes at level l (n_L = 1). Level l supplies w*n_{l+1} -
n_l nodes, so the total is sum_{l=0}^{L-1} (w n_{l+1} - n_l) =
(w-1) sum_{l=1}^{L-1} n_l + w - n_0. Each n_l <= min(n_0, capacity_l), where
capacity_l is the number of level-l nodes over the occupied leaf range
(2^(18-l) for C1/C2; for the folded tree, whose openings lie in the first
2^16 of the padded 2^18 leaves, 2^(16-l) and 1 for l >= 16). The expression
is maximal at n_l = min(n_0, capacity_l) with n_0 the batch size (a smaller
distinct count lowers every term by at least as much as it removes); for
binary: C1/C2 146 (10) and 172 (12), folded 128 and 150, total 914. Duplicate
folded indices only lower n_0. The bound is attained (bit-reversed index
sets, asserted) and 20,000 random batch sets never exceed it (max 903). The
padding leaves of the folded tree stay committed and authenticated exactly as
in the shipped tree.

## 2. Prototype and teeth (measurement 5)

Candidate code (feature `compact-binary`, default off, implies
`private-leaf-salts`), all in `crates/aspis-r1-cost-probe`:

- `src/multiproof.rs`: binary tree (`BINARY_NODE_TAG = 0x12 || left ||
  right`, a new domain separator; leaves unchanged `0x10 || tag || values ||
  salt`), multiproof generation and a strict verifier (strictly increasing
  indices, exact node consumption, root and single-top checks), node counting.
- `src/compact.rs`: compact codec and the fixed-length stored layout
  (57,607 bytes; six zero-padded node slots).
- `src/candidate.rs` (child module of `verifier`, appended after every
  shipped item): `parse_shape`, strict canonical scan, logical rebuild of the
  semantic rows and `y1` (zero high halves) before `Prefix::parse` and any
  hash, batch multiproof checks, the shipped fold/accumulate/relation code,
  `checkpoint`/`resume` over the compact stored bytes.
- `src/host_commitment.rs`, `src/prover.rs` (host only): C1/C2 commitments
  under a binary tree on request, the folded tree (still the padded 2^18
  leaves with salted padding) binary, and `prove_masked_{fixture,attempt}_candidate`
  emitting the stored layout. The shipped prover paths are unchanged in
  behaviour (the extra `binary` flag is false on them).

Fiat-Shamir: every transcript message has its shipped byte definition (the
semantic records and `y1` are hashed in their rebuilt logical 32-byte form).
Because the C1, C2 and folded roots are binary-tree roots, the C1-time
binding, the C2 record, the alpha1 message and hence every challenge after
them differ from the eight-way proof for the same witness. This is expected.

**Six fixtures re-proved** (`native-s2.json`): the Pool B1 measurement driver
patched by `harness/patch_driver_candidate.py` (feature `compact-binary`,
`pool_gate` sha256 915b310d...) re-proves each fixture's witness (`--pairs N`,
kind, fresh OS entropy, split 10); the generated ASF8 equals the saved
fixture's public file byte for byte in all six; the candidate stage 1, strict
stage 2 and authenticated stage 2 accept natively. Stored bytes 57,607 for
all; the variable-length equivalents (actual node counts) are:

| Fixture (re-proved) | Nodes per slot [C1A,C2A,FA,C1B,C2B,FB] | Nodes | Variable bytes |
|---|---|---:|---:|
| transfer-13 | 144,144,126,155,155,133 | 857 | 55,783 |
| transfer-255 | 132,132,114,169,169,147 | 863 | 55,975 |
| transfer-1023 | 145,145,127,164,164,142 | 887 | 56,743 |
| withdrawal-13 | 146,146,128,166,166,144 | 896 | 57,031 |
| withdrawal-255 | 134,134,116,152,152,130 | 818 | 54,535 |
| withdrawal-1023 | 134,134,116,167,167,145 | 863 | 55,975 |

(Query sets differ from S1's because the roots, and so the queries, differ.)

**Teeth** (`examples/proof_size_s2.rs`, `teeth.json`, on the deterministic R0
fixture; the candidate and the shipped control both accept). Each mutation is
run through stage 1 and, where stage 1 still accepts, a fresh checkpoint and
stage 2, so batch-B mutations are rejected by stage 2:

| Mutation | Result |
|---|---|
| wrong sibling hash, each of the six slots | Merkle |
| missing node (last real node removed), slots 0, 2, 3, 5 | Merkle |
| extra node (non-zero word after the real nodes), slots 0, 4 | Parse |
| any non-zero padding byte | Parse |
| two openings swapped (misordered leaf indices), batch A and B | Merkle |
| one opening duplicated over another, batch A and B | Merkle |
| semantic value stored in 32-byte form with non-zero high half | Parse (length) |
| y1 value with an injected high half, length kept | rejected (Parse) |
| non-canonical compact limb (2^31-1), semantic and y1 | Parse |
| encoder given a logical value with non-zero high half | refuses (NonZeroHigh) |
| checkpoint whose proof hash is over the expanded bytes | Checkpoint |
| expanded bytes presented as the proof | Parse |
| stage 1 split 11; shipped proof to candidate; candidate to shipped | Parse |
| proof byte changed after stage 1 | Checkpoint |

Index-level teeth for the multiproof verifier (duplicated and misordered
index lists, missing and extra node, wrong sibling) are unit tests in
`multiproof.rs`; all 18 crate unit tests pass with the feature on.
Interpretation of "non-zero byte where a zero half is implied": the stored
format carries no high half, so the reachable forms are a high half inserted
into the stored bytes (strict length / canonical rejection) and a logical
value with a non-zero high half, which has no compact encoding.

## Before S3: where the time goes

S3 adds a `compact-binary` feature to `programs/r1-cost-probe` (adapter
stage 1/stage 2 and buffer lengths switch to the candidate), one SBF build of
the candidate verifier and one of the default verifier for the identity
check (each ~5-10 min compile), the stack audit, and six full replays
(prove ~6 s + LiteSVM, seconds each). Estimate 2-3 hours, below the 6-hour
limit.

## 3. Compute (measurement 2)

(pending)

## 4. Uploads (measurement 3)

Uploaded body = 688-byte candidate afterstate + proof (the ASPU body the
stage-1 adapter requires). Chunk sizes in source at the base:
`tools/r1-cost-probe/src/bin/pool_gate.rs` `LIFECYCLE_UPLOAD_CHUNK_BYTES =
900` (TxV1) and `TXV0_UPLOAD_CHUNK_BYTES = 800` (TxV0); the wallet's
`V7_POOL_PROOF_UPLOAD_CHUNK_BYTES = 960`
(`crates/aspis-pool-wallet-v1/src/verifier_transaction_builder.rs:55`, the
V5 figure 79 = ceil(75,358 / 960)).

| Body | bytes | at 900 (TxV1 driver) | at 800 (TxV0 driver) | at 960 (wallet V7) |
|---|---:|---:|---:|---:|
| shipped proof | 125,031 | 139 | 157 | 131 |
| candidate (fixed 57,607) | 58,295 | 65 | 73 | 61 |

Transaction size limits in the pinned sources: TxV1
`solana_message::v1::MAX_TRANSACTION_SIZE = 4096`
(`solana-message-4.4.1/src/versions/v1/mod.rs:36`), applied by
`agave-transaction-view-4.2.1/src/sanitize.rs:46` for
`TransactionVersion::V1`; legacy/V0 `solana_packet::PACKET_DATA_SIZE = 1232`
(`solana-packet-4.2.0/src/lib.rs:42`, same `sanitize.rs:45`). The counts at
the TxV1 and legacy maxima net of the measured upload-instruction overhead
are below (S3).

## 5. Parameters (measurement 4)

(pending)

## 6. Obligations (measurement 6)

See `design/PROOF-SIZE-OBLIGATIONS-20261019.md`.

## Runs

Receipts under `receipts/` (command, exit, wall, peak RSS, swaps, cgroup
limits) per host run.
