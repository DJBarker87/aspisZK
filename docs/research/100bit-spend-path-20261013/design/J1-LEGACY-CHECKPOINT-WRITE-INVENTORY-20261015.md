# Legacy checkpoint writes and Pool proof-account layout

> Note (2026-10-19): the R1 proof format is now the compact binary-multiproof format, fixed length 57,607 bytes (`../evidence/format-adopt-20261019/REPORT.md`); 124,343 bytes below is the retired eight-way format.

Read-only source inventory of the account write interfaces relevant to the
entrypoint boundary in `J1-ENTRYPOINT-SCOPE-DECISION-20261015.md`. This records
the sizes, byte ranges, dispatch paths, and error-before-write behavior visible
in the cited Rust. It is not a Lean theorem or a proof that no other runtime
component can mutate these accounts.

## Literal legacy instruction path

In `programs/r1-cost-probe/src/lib.rs:31–38`, feature-enabled adapter
dispatch happens first for leading bytes 4, 5, or 6, exact instruction bytes
`[3,10]` and `[3,11]`, or any byte string beginning `ASQ8`. Everything else
must match three-account `[1,k]` with `k ≤ 22` or `[2]`, then pass owner,
executable, and writable checks before borrowing account 3 mutably. Thus the
legacy instructions remain reachable in the selected build.

Legacy `[1,k]` (`lib.rs:40–44`) first requires the entire checkpoint account
to be zero, calls `first`, and only then compares the whole account length to
the returned checkpoint vector length. A mismatch returns
`InvalidAccountData` before `copy_from_slice`; on success the whole account is
replaced by the returned checkpoint. `first` calls `verifier::tx1`
(`lib.rs:24–28`), whose `checkpoint` result has exactly
`verifier::checkpoint_size(variant)` bytes (`verifier.rs:302–316`). The
checkpoint size is `CHECKPOINT_FIXED + 16 * final_len` (`verifier.rs:18,25`);
`CHECKPOINT_FIXED` is 744 bytes. The source definitions in `transport.rs:5–9`
give `final_len(S1)=256`, and `final_len(S2)=final_len(D)=64`, hence the
whole-account checkpoint sizes are 4840 bytes for S1 and 1768 bytes for S2 or
D.

Legacy `[2]` (`lib.rs:45–48`) passes the entire third account as the
checkpoint to `verifier::tx2`. `resume` first checks exact checkpoint length,
magic, tag, and header fields, and returns `Error::Checkpoint` if any fail
(`verifier.rs:325–328`). Only after `tx2` succeeds does the caller change byte
10 and recompute the trailing checksum (`lib.rs:46–47`). Therefore its
account write is also whole-account, and the mismatch/error path precedes any
mutation.

## Pool proof account and tail writes

The Pool adapter fixes `ASPU_HEADER = 40` and
`CHECKPOINT_TAIL_BYTES = 1768` (`r1_pool_adapter.rs:51–55,87`). Its S2 proof
body is laid out as:

```text
40-byte ASPU header
+ 688-byte verified-afterstate envelope
+ S2 proof bytes
+ 1768-byte checkpoint tail
```

The afterstate envelope is `8 + 680 = 688` bytes
(`crates/aspis-statement/src/pool_v1/pair_terminal.rs:37–40`). The S2 proof
length is `verifier::View::proof_bytes(Variant::S2) = 124343` under the pinned
P3/private-salt configuration. Consequently the wrapper account is 126839
bytes total, with the checkpoint tail at offsets 125071 through 126838.
`stage1` checks that exact whole-account length, ASPU magic, encoded body
length, S2 tag, candidate bytes, and a zero checkpoint tail before calling
`first` (`r1_pool_adapter.rs:899–929`). It writes only the 1768-byte tail,
and only after `first` succeeds and returns exactly 1768 bytes
(`:929–935`). Its failure branches before the copy leave that tail unchanged.

`stage2` recomputes the candidate/proof/tail offsets and checks the exact
account length and encoded body length (`r1_pool_adapter.rs:949–964`); it
passes only the tail slice to `tx2_authenticated` (`:970–977`). The ASQ8
scanner likewise checks exact full wrapper size and tail length
(`r1_pool_adapter.rs:688–723`).

This distinction is mechanically relevant: legacy `[1,k]` has an exact
whole-account checkpoint-length equality with one of 4840 or 1768 bytes,
whereas the Pool S2 account is a 126839-byte wrapper and its checkpoint is a
1768-byte suffix. Legacy `[1,k]` cannot pass its copy length guard on that
Pool-sized account. Legacy `[2]` cannot pass `resume`'s whole-account length
check on that account, so its later byte-10/checksum writes are unreachable
there. These are source-level size and ordering observations only.

## Lifecycle instructions sharing adapter dispatch

Adapter instruction 4 initializes a lifecycle proof account only when its
whole length is exactly `40 + body_len` and every byte is zero; for proof kind,
`body_len = 688 + proof_bytes(S2) + 1768` (`r1_pool_adapter.rs:95–127,
277–298`). Instruction 5 validates the exact ASPU header, body length and
authority, then requires `offset + payload.len()` to be no greater than the
proof writable prefix `688 + proof_bytes(S2)`; the copy begins after the
40-byte header (`:302–335`). The checkpoint suffix is outside that writable
prefix. Instruction 6 validates the proof body and requires the tail to be
all zero before zeroing the authority bytes (`:242–273,339–359`).

Pool stage 1 requires the authority header bytes to be zero
(`r1_pool_adapter.rs:908–910`) before it writes the tail. Conversely,
instruction 5's unsealed-header validation requires the stored authority to
match a nonzero authority key (`:229–238,317–325`). These checks describe the
ordering and ranges of the adapter's own lifecycle writes. This inventory
does not turn them into an account-provenance theorem or a claim about every
external CPI/runtime writer.

## Source pins

The inspected review worktree is at `3944eaa5cfdcfff8867d8a46437c02613366e201`.
The key files have these SHA-256 hashes:

| File | SHA-256 |
|---|---|
| `programs/r1-cost-probe/src/lib.rs` | `294546036e6cf8bb8dcc1f1f4a65c5e0887ac04593cdda801f58c75a284d582a` |
| `programs/r1-cost-probe/src/r1_pool_adapter.rs` | `b2adab8610189a5031fc6f28a7cdeef12c01aa292423743cb4696aa3ee1590a4` |
| `crates/aspis-r1-cost-probe/src/verifier.rs` | `2cab573be46ca69b5d82837e5221a9a499d3b6dc1f89b801e388b4e8b1fe01cd` |
| `crates/aspis-r1-cost-probe/src/transport.rs` | `34af7f077fdae8147ebd79a44e7acb38395ec440115109c8fbfc654cb2c1e8c7` |
| `crates/aspis-statement/src/pool_v1/pair_terminal.rs` | `820710b2284ea967bb4b9a6d2ceb6cb171ac185b01df816db99db6ea78e629a3` |
