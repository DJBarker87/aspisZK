# Authenticated second-stage parsing: source audit

Root audit, 2026-10-13. The reviewed optimization is `View::parse_shape` plus
`tx2_authenticated`, first committed in 628054cd494c66dc91e4e01612c70bd164ecf276.
The optional P3 diff adds salts and changes framing/domain constants; it does
not change the trust argument below. This is a source-level audit and an
explicit invariant argument, not a compiled source-semantics theorem.
The exact source hashes reviewed are recorded in
[`AUTHENTICATED-PARSER-AUDIT-SOURCES.json`](AUTHENTICATED-PARSER-AUDIT-SOURCES.json).

## Precisely what is claimed

Let P be the exact proof byte string successfully parsed and verified by
stage one, X its full encoded ASF8 public statement, and C the checkpoint
produced by that execution. If stage two receives that authentic C and the
same P and X, the skipped canonical checks would all pass. Its remaining
arithmetic therefore uses exactly the canonical values the strict parser
would have decoded. The strict and optimized paths run the same `resume`,
query geometry, remaining queries, and `finish_relation` functions.

Alternatively, when identity is established by SHA-256 digests, this claim
holds outside the explicitly charged event of different byte strings having
the same digest. No numeric reduction or field-value equality substitutes
for byte equality: all byte encodings, headers and records are bound.

**The checkpoint checksum is an unkeyed hash, not a MAC.** Hash checks alone
do not establish that C was produced by stage one. Both strict `tx2` and
`tx2_authenticated` require checkpoint provenance. Strict parsing cannot
reconstruct already-completed semantic verification or already-accumulated
queries from an attacker-created checkpoint. The optimized API must never
be used as a verifier for arbitrary externally supplied checkpoint bytes.

## Coverage of every proof region

| Proof region | Stage-one validation | Stage-two use / justification |
| --- | --- | --- |
| Header, variant, reserved bytes, exact total length | `View::parse` calls `parse_shape` | Shape checks are repeated before slicing. |
| Semantic prefix, 27 framed records | `r1_semantic::verify_observed` and `r1_wire::Prefix` validate tags, lengths, all field encodings and the QM31-subfield restriction | Stage two does not re-run this prefix; derived roots, challenges and claims come from C. The entire prefix remains inside the proof digest. |
| 29 second-circle lane values | `echeck(y1,true)` checks each WideExact encoding and zero high QM31 component | Derived batched claim is in C; bytes remain bound. |
| Inactive scalar | `WideExact::from_le_bytes` during shape parse | Canonical decoding is repeated even in `parse_shape`. |
| Seven first-round coefficients | `echeck(round0,false)` | `finish_relation` decodes these same bytes and evaluates the round polynomial. |
| Intermediate root | Fixed 32-byte slice | Used only as a hash digest; no field canonicality requirement. |
| Seven second-round coefficients | `echeck(round1,false)` | Same argument as first-round coefficients. |
| All 64 final-message values (S2) | `echeck(final_message,false)` | Pairing and residual dot product decode the same canonical WideExact bytes. |
| All 22 initial opening records | For each of four slots: 26 canonical M31 values, canonical QM31 D, and two canonical QM31 H1/G values | `fast_dots` and query arithmetic consume the same fields. This scan covers **all 22 records**, including those deferred to tx2. |
| All 22 second-fold opening records | Four canonical WideExact values per record via `echeck` | Line folding and selected-child comparisons consume these same values. |
| Authentication paths; P3 opening salts | Fixed lengths/slices; arbitrary digest/salt bytes are permitted | Merkle hashing authenticates them. They are not interpreted as field elements. |

`echeck` uses 32-byte chunks. Every slice passed to it has a structurally
fixed length divisible by 32, so it cannot silently omit a partial tail.
`View::proof_bytes` and the exact-length test exclude trailing bytes. The
query widths are fixed, not taken from unchecked input counters.

The proof digest stored in C covers the complete proof slice, including all
22 queries, both round polynomials, final message, semantic records and all
path/salt bytes. It excludes the outer ASPU header, candidate and checkpoint
tail by design; those have separate account/candidate checks below.

## Checkpoint fields are decoded again

`resume` checks exact checkpoint length, magic, variant, status, reserved
bytes, and next-query index <=22. Before returning it compares SHA256(P),
SHA256(X), and the checkpoint checksum. It then canonically decodes gamma,
kappa, both fold alphas, rho, ten semantic alphas, both circle coordinates,
claim, accumulated right-hand side, accumulated power and all K weights.
All 22 query indices are checked for range and distinctness. Reader length
must finish exactly at the checksum boundary.

The shape parser only performs bounded slicing and canonical conversion of
the inactive scalar before `resume`. All unchecked proof-field arithmetic
occurs after successful checkpoint/digest validation. The mutation gate
specifically sets a query M31 word to 0xffffffff and confirms hash rejection
before arithmetic; strict tx2 rejects it at parsing instead.

## Runtime provenance and immutability invariant

The invariant is for an account that starts zeroed and is governed throughout
by the audited program version:

1. `[4,kind]` initializes only an entirely zeroed, exactly sized account owned
   by the verifier. It records a nonzero signer upload authority.
2. `[5,offset,payload]` requires that authority and permits writes only in the
   body prefix. For an ASPU proof, the allowed prefix ends **before** the
   checkpoint tail. Bounds use checked addition. Header writes and tail
   writes, including straddling writes, are excluded.
3. `[6]` validates the proof/candidate or canonical public statement, requires
   a zero checkpoint tail, and clears the authority. Subsequent upload or
   finalize attempts fail because they require a nonzero matching authority.
4. Adapter stage one accepts the sealed proof and sealed ASRU public buffer,
   distinct accounts and the correct ownership/privileges. It checks the
   candidate equals the candidate encoded in X, that the S2 tail is zero,
   and calls `first`, which derives the semantic Public object from X.
   Only after strict parsing, semantic verification and the first k queries
   succeed does it write C into the tail. It never writes the proof prefix.
5. Adapter stage two requires the proof account to be verifier-owned,
   non-executable and read-only. It authenticates the registry, Pool/master,
   anchor and current selected lane, reconstructs X from those accounts and
   the ASQ8 request/candidate, encodes X, and uses its digest in `resume`.
   A stale/current-statement substitution therefore fails the X binding.
6. The proof data remains immutably borrowed during resumed verification.
   This program makes no CPI capable of modifying it. Solana account locking
   and read-only privilege enforcement supply the runtime isolation.

Registry checks require the pinned release/policy and immutable deployment
and registry. Replay is stopped by Pool's nullifier consumption, not by
pretending the read-only checkpoint is consumed in stage two.

## Audit of other writers

`programs/r1-cost-probe/src/lib.rs` has two legacy measurement instructions in
addition to the lifecycle/adapter dispatcher:

- `[1,k]` writes only its third account, requires it entirely zero, runs strict
  `first`, and requires its total length to equal the checkpoint length before
  copying. A finalized ASPU is nonzero and much larger; an ASRU also has the
  wrong length. It cannot write an embedded ASPU tail.
- `[2]` requires successful strict tx2 before changing status byte 10 and its
  checksum in that third account. `resume` requires that account's entire
  length to be the checkpoint size; it cannot treat an ASPU/ASRU as a tail.

The program has no close, realloc, arbitrary header write, authority-reset or
CPI writer entrypoint. Lifecycle init cannot reinitialize a sealed account.
The account-owner runtime disallows a foreign program modifying these data,
and transferring ownership requires zeroed data. This was checked against
the pinned `solana-transaction-context-4.2.1/src/instruction_accounts.rs`,
SHA256 `d55be03bca6708e41b5d92a3fc24da0791c0d0bfb89cd4cc2e4969d6f91bdc79`,
functions `set_owner` and `can_data_be_changed`. The corresponding upstream
[source](https://github.com/anza-xyz/agave/blob/master/transaction-context/src/instruction_accounts.rs)
also exposes those rules; the pinned local dependency is the version used
for this audit.

## Deployment-history qualification discovered by this audit

Checking that a program is immutable *now* does not prove that arbitrary
pre-existing program-owned bytes were created by the audited code. An older
malicious version could have manufactured a sealed account and checkpoint
before its upgrade authority was removed. This caveat applies to the
original checkpoint verifier as well as the parser optimization.

A production release must establish the account-state invariant from a
trusted deployment genesis (for example a fresh program deployment whose
entire writable history uses the audited lifecycle), or provide an explicit
migration/provenance mechanism. The current LiteSVM fixtures start with the
audited code and zeroed upload accounts. They do not establish a live
program's deployment history. No live release is approved by this audit.

## Evidence and limits

The focused authenticated gate verifies valid strict/optimized acceptance
and equality of 9253 traced arithmetic entries, plus proof/public/checkpoint
mutations and noncanonical query rejection. Pool lifecycle gates cover tail
injection and straddling, wrong authority, repeated init/finalize, post-seal
writes, malformed finalization and unsealed stage-one input. Runtime cases
also exercise changed proof after checkpoint creation, wrong release, stale
lane, replay and token-CPI rollback.

These tests support the audited invariant; they do not replace it, prove
all Rust memory semantics, prove SHA-256 binding, or close R1 soundness/ZK.
Any new account writer, upgrade path, proof layout, parser branch or use of
`tx2_authenticated` must be reviewed against this coverage again.
