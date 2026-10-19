# J1 verifier dispatch and hash-route inventory

> Note (2026-10-19): the R1 proof format is now the compact binary-multiproof format, fixed length 57,607 bytes (`../evidence/format-adopt-20261019/REPORT.md`); 124,343 bytes below is the retired eight-way format.

Read-only source inventory for the proposed configuration boundary in
`J1-CONFIG-BOUNDARY-PROPOSED-20261015.txt` (available at review commit
`95bf664bc`; the proposal pins Rust source revision
`136b746805f3438507732622c9b4e50f36bf49f9`). No build was run. The verifier
and adapter source files below are unchanged from that source revision in the
review worktree; this note records dispatch and helper routes, not a proved
execution bound or source refinement.

## Entrypoint and feature routing

`programs/r1-cost-probe/Cargo.toml` makes only `custom-heap` default (lines
9–15). `pool-adapter` and `private-leaf-salts` must be selected explicitly;
the program dependency enables `aspis-r1-cost-probe/optimized-terminal`
(lines 16–20). Thus the proposed pool configuration is a selected build
configuration rather than the crate's default dispatch behavior.

At `programs/r1-cost-probe/src/lib.rs:31–38`, when `pool-adapter` is enabled,
first-byte 4/5/6, exact `[3,10]` or `[3,11]`, and any `ASQ8` prefix are routed
to `r1_pool_adapter::process`. Otherwise the public entrypoint admits only
three-account legacy data `[1,k]` for `k=0..22` or `[2]`; it then checks account
owners, executable flags and write permissions before borrowing proof,
public and checkpoint data (`:36–38`). With the adapter feature off, all
adapter routes fall through to the legacy allowlist and reject.

The adapter dispatch (`programs/r1-cost-probe/src/r1_pool_adapter.rs:982–993`)
selects lifecycle operations 4/5/6, exact stage-1 `[3,10]`/`[3,11]`, and sends
every other adapter-routed instruction to stage 2. Stage 2 first checks six
accounts and the ASQ8 request magic (`:940–948`); `validate_asq8` then checks
exact request size and profile/release/pool bindings (`:807–842`). The wrapper
also authenticates pool, registry, entry, checkpoint and lane state. That path
uses multiple `Pubkey::find_program_address` calls (`:481–521`, `:538–566`,
`:618–665`) before calling the verifier. Those SDK PDA derivations are outside
the verifier's supplied `HashFn`/`hashv` closure, but would need separate
accounting in an all-program SHA/compute statement.

## Proposed Pool stage 1 and stage 2

Stage 1 is exact `[3,10]` or `[3,11]` with two accounts. It validates the
public wrapper and statement, verifies a fixed AS PU body length, fixed proof
length for `Variant::S2`, the AS PU magic/header and S2 tag, and an all-zero
checkpoint tail before calling `first` (`r1_pool_adapter.rs:868–929`). It
writes the resulting checkpoint only after `first` succeeds and its length is
checked (`:929–935`). `first` decodes the public statement and calls
`verifier::tx1` with `hashv` and the local logging observer (`lib.rs:24–28`).
The stage-1 implementation performs its own proof framing checks; it does not
call `scan_aspu_body`.

Stage 2 calls `validate_asq8`, which uses `scan_aspu_body` to require exact AS
PU body size, S2 tag and candidate-afterstate framing (`r1_pool_adapter.rs:688–729`,
`:807–842`). It checks body length again, reconstructs and encodes the public
statement at its fixed size, then calls `verifier::tx2_authenticated` with
`hashv` (`:939–978`). The authenticated entrypoint uses `View::parse_shape`
(rather than the strict canonical field scan) and then `resume`, queries the
remaining range, and finishes the relation (`verifier.rs:368–385`). Its source
comments require authentic `tx1` checkpoint provenance and proof immutability;
`resume` itself only checks hashes plus an unkeyed checksum (`:368–378`).

Under the proposed P3/private-salt feature, S2 proof shape is exactly 124,343
bytes: `View::proof_bytes` and the parser's exact-length check are at
`verifier.rs:37–58`; `Variant::S2` has two folds and final length 64
(`transport.rs:3–9`). The S2 checkpoint is 1,768 bytes (`verifier.rs:18,25`).
These shape checks happen before the verifier hash calls on this route. The
pool request and wrapper impose their own exact framing, but they do not make
other entrypoint or direct library routes unreachable.

The verifier hash constructors on a successful admitted Pool pair are:

- Semantic initialization: one call with `[DOMAIN, [0], public-length-u32,
  public_bytes, c1_root]` after semantic prefix parsing and a u32 public-length
  check (`r1_wire.rs:173–180`; caller `r1_semantic.rs:70–77`).
- Each semantic/circle row: absorb `[state, [0,0xa0+row], framed_record]`,
  squeeze `[absorbed,[1]]`, and advance `[absorbed,[2]]` (`r1_wire.rs:189–212,
  215–241`). Prefix parsing fixes 27 records and exact row framing before this
  (`r1_wire.rs:265–293`); semantic verification may reject on a boundary or
  terminal check before later rows (`r1_semantic.rs:83–130`).
- Transcript initialization and challenges: one init hash `[domain,variant-tag,
  semantic_state]`; each scalar row absorbs with a u32 payload length, then
  squeezes and advances; query sampling absorbs once and makes eight
  squeeze/advance pairs (`transcript.rs:7–45`). For S2, `Prepared::new` uses
  rows 27–32 and query row 31 (`verifier.rs:85–112`).
- Per opened S2 query, each C1/C2 salted leaf is one hash and each six-level
  eight-way path has six parent hashes. The optional folded-tree leaf and its
  six-level path add seven more hashes. The exact call grammar is in
  `state_only_private_merkle.rs:22–35` and `r0/merkle.rs:17–31`; calls and
  short-circuit Merkle rejection are in `verifier.rs:120–128,242–263`.
- Checkpoint creation hashes proof, public bytes, and checksum body (`verifier.rs:302–316`). Resume checks fixed checkpoint shape first, then hashes proof,
  public (only if proof digest matched), and checksum (only if both earlier
  checks matched) (`:325–339`). Query/Merkle/relation errors can stop execution
  after different prefixes of these calls.

For the selected Pool path with S2, successful stage 1 at k=10/11 plus stage 2
completes 22 queries. The proposal's arithmetic of 82 semantic calls, 33
opening-transcript calls, 462 query/Merkle calls, and 3 checkpoint-write plus
3 resume calls describes that paired route's verifier `HashFn` sites. It is
source arithmetic only; this note does not prove call alignment or a universal
bound. Stage-2 PDA derivations above are not included in that count.

## Routes still present beside the proposed Pool route

The Pool feature does not disable the same program's legacy instructions.
`lib.rs:33–36` routes `[1,k]` and `[2]` to the legacy branch whenever the
adapter did not match. Legacy `[1,k]` calls `first`/`tx1`, then stores its
checkpoint (`:40–44`). Legacy `[2]` calls strict `tx2`; after successful
verification it changes checkpoint byte 10 and performs another
`hashv([b"UNPROVED:R1:checkpoint", checkpoint[..end]])` before writing the
checksum (`:45–48`). This is an additional same-program checkpoint-write hash
not present in the proposed Pool stage-2 adapter. Legacy dispatch does not
restrict the proof variant to S2: `View::parse` accepts S1/S2/D tags
(`verifier.rs:44–46`; `transport.rs:3–9`). The S2-only Pool restriction
therefore does not bound legacy inputs.

There are also public library helpers outside instruction dispatch:
`View` has public fields and `Prepared::new`, `query`, `checkpoint`, `resume`,
`tx1`, `tx2` and `tx2_authenticated` are public (`verifier.rs:27–30,85–112,
237–240,302–340,342–386`). `Transcript::{new,absorb,block,scalar,scalar_k,
queries}` are public (`transcript.rs:5–45`). In particular, `absorb`,
`block`, `scalar`, `scalar_k` and `queries` accept arbitrary payload slices;
`absorb` hashes the full payload while only casting its length to u32
(`transcript.rs:14–20,35–45`). `SemanticTranscript::new` has a u32-conversion
failure before its first hash, but no S2-size bound at that helper boundary
(`r1_wire.rs:173–180`). `checkpoint` hashes arbitrary caller-supplied proof
and public slices before asserting its generated checkpoint size;
`resume` hashes caller-supplied proof/public slices after only checking the
checkpoint's own fixed shape (`verifier.rs:302–339`). `Prepared::new` can be
called on a manually constructed public `View`, so parser-imposed slice sizes
are not inherent to that helper API.

The lifecycle 4/5/6 operations are dispatch-reachable when the feature is on;
they initialize, write and finalize wrapped proof/public accounts
(`r1_pool_adapter.rs:276–360`). They contain no call to the verifier's supplied
`HashFn`, though they can create or mutate inputs consumed later. The ASQ8
stage-2 authentication path also contains SDK PDA derivations noted above.

## Boundary facts for a theorem statement

The proposed Pool-route predicate is a strict subset of live source dispatch.
A theorem limited to its `HashFn` callsites needs an explicit caller/config
boundary that excludes legacy `[1,k]`/`[2]`, or separately covers them (including
the post-tx2 checksum rehash), and excludes direct helper APIs or supplies their
length premises. If “hash calls” includes all SHA operations, it also needs a
separate account/PDA-hashing model for `find_program_address`. A callback
assumption should pin the local `mark` observer (which logs only), since the
public library functions accept an arbitrary observer function pointer.

No source-shape bound, public source/refinement link, checkpoint authenticity,
all-route hash bound, or release conclusion is established by this inventory.

## Source pins for this inventory

The inspected checkout is `f1edebd66d8ea21178b8f4f34b4c623fc3934413`.
The relevant Rust files are byte-identical to proposal pin
`136b746805f3438507732622c9b4e50f36bf49f9`; current SHA-256 values are:

| File | SHA-256 |
|---|---|
| `Cargo.lock` | `f93f8f524fdd707c7a3b7feade31d015c891264b6c8fbd8bff885249e19600ea` |
| `programs/r1-cost-probe/Cargo.toml` | `1208d93c95f3e4e769fd1ba48f71bbb031c4ddd33793f09f5cc6405fe9da71f1` |
| `programs/r1-cost-probe/src/lib.rs` | `294546036e6cf8bb8dcc1f1f4a65c5e0887ac04593cdda801f58c75a284d582a` |
| `programs/r1-cost-probe/src/r1_pool_adapter.rs` | `b2adab8610189a5031fc6f28a7cdeef12c01aa292423743cb4696aa3ee1590a4` |
| `crates/aspis-r1-cost-probe/Cargo.toml` | `5fafcd2572896d4ba35cb01304aa6ccde1d0b634804fedf22c3f74133cedf093` |
| `crates/aspis-r1-cost-probe/src/verifier.rs` | `2cab573be46ca69b5d82837e5221a9a499d3b6dc1f89b801e388b4e8b1fe01cd` |
| `crates/aspis-r1-cost-probe/src/r1_wire.rs` | `73f4b49dfae90be8a5cafd9d69eaf9ed06a01009f3daabc5627b42e6cf31c996` |
| `crates/aspis-r1-cost-probe/src/transcript.rs` | `c91ffe824a55ff62659e8a194d2ea201032383e4e11e5f60625404a30c691ef6` |
| `crates/aspis-r1-cost-probe/src/r1_semantic.rs` | `964f008a0841246fe3638ce2e492d12d18d78302565aa57f8c7df4d079579ce3` |
| `crates/aspis-core/src/r0/merkle.rs` | `6df6b25bf5b29dd2744af9db645e3c5818fa9256a454f175db4b750919ce7224` |
| `crates/aspis-core/src/state_only_private_merkle.rs` | `f0edc31d07d30f5b19fcaf872fba18678d13d1ba5fac1199f1f4d2be74c74f9b` |
