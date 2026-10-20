> R1 update (2026-10-20): the R1 pair-forest marker path is no longer the
> nullifier-marker PDA path described below. B1 uses `create_with_seed` under
> the forest master; see [the accepted B1 review](LEAD-REVIEW-POOL-B1-20261019.md)
> and its freshness premise. Historical results and legacy PDA routes are unchanged.

# J1 adapter, verifier, and Pool call-site inventory

Inspection base: `3c79ec30fa44f408c716bb345050c137e907fa67` (worktree HEAD).
This is a mechanical source/call-site map. It does not set a final shared-oracle
budget, prove a source refinement, or infer cryptographic closure. “HashFn”
means the supplied `&[&[u8]] -> [u8; 32]` callback; `hashv` consumes the listed
slices as one SHA-256 input. Solana PDA APIs also perform SHA work internally,
but are listed separately because they are not calls through that callback.

## Runtime source pins

| File | SHA-256 |
|---|---|
| [`lib.rs`](../../../../programs/r1-cost-probe/src/lib.rs) | `36d36ee707f565df675db2ef7b2d27467f8b79bb99142c4b21d6fb7cc81910c9` |
| [`r1_pool_adapter.rs`](../../../../programs/r1-cost-probe/src/r1_pool_adapter.rs) | `b2adab8610189a5031fc6f28a7cdeef12c01aa292423743cb4696aa3ee1590a4` |
| [`verifier.rs`](../../../../crates/aspis-r1-cost-probe/src/verifier.rs) | `2cab573be46ca69b5d82837e5221a9a499d3b6dc1f89b801e388b4e8b1fe01cd` |
| [`transcript.rs`](../../../../crates/aspis-r1-cost-probe/src/transcript.rs) | `c91ffe824a55ff62659e8a194d2ea201032383e4e11e5f60625404a30c691ef6` |
| [`r1_wire.rs`](../../../../crates/aspis-r1-cost-probe/src/r1_wire.rs) | `73f4b49dfae90be8a5cafd9d69eaf9ed06a01009f3daabc5627b42e6cf31c996` |
| [`r1_semantic.rs`](../../../../crates/aspis-r1-cost-probe/src/r1_semantic.rs) | `964f008a0841246fe3638ce2e492d12d18d78302565aa57f8c7df4d079579ce3` |
| [`state_only_private_merkle.rs`](../../../../crates/aspis-core/src/state_only_private_merkle.rs) | `f0edc31d07d30f5b19fcaf872fba18678d13d1ba5fac1199f1f4d2be74c74f9b` |
| [`r0/merkle.rs`](../../../../crates/aspis-core/src/r0/merkle.rs) | `6df6b25bf5b29dd2744af9db645e3c5818fa9256a454f175db4b750919ce7224` |
| [`pair_forest.rs`](../../../../programs/aspis-pool/src/pair_forest.rs) | `d96b352bae081a72d6e887759a356674598e0bf3a177c8d103885f02bc344c30` |
| [`pair_forest_dispatch.rs`](../../../../programs/aspis-pool/src/pair_forest_dispatch.rs) | `7e45910a3d64e328dc234ede290119770e898bcb48f277d978219740ec891514` |
| [`processor.rs`](../../../../programs/aspis-pool/src/processor.rs) | `3c989ba201b622c01e67edec7cba8b17ba30663b386a4f316e757ff06dad7354` |
| [`nullifier.rs`](../../../../programs/aspis-pool/src/nullifier.rs) | `274398d59536f19fa25dd11269945893fe02a03e5668655244b7be2f32e26c6f` |
| [`history.rs`](../../../../programs/aspis-pool/src/history.rs) | `7d754900fecb4d6ba4511029a3617e90f91c697fc415fabd8aa4b2c0c519107a` |
| [`registry.rs`](../../../../programs/aspis-pool/src/registry.rs) | `99c166a1f6641631937450fe7e59e08cb6422e588d8c49b90f66f9a4cb85ed8a` |
| [`prepared_settlement.rs`](../../../../programs/aspis-pool/src/prepared_settlement.rs) | `4b7dfa3741edfdcc2d33a62401fdbe280e332c206a59f6df0ca779dead85e606` |
| [`prepared_settlement_format.rs`](../../../../programs/aspis-pool/src/prepared_settlement_format.rs) | `dd7306f9639d4c1c9c9f77f5868fa83e59e3967721f812c7f458ee2b789d816a` |

The existing [verifier input-length inventory](J1-HASH-INPUT-LENGTH-INVENTORY-20261015.md)
and [raw query-call inventory](../QUERY-CALL-INVENTORY.md) give the detailed
S2 preimages and bounded verifier loops. The latter's successful two-phase
verifier subtotal is 583 raw `HashFn` calls for the inspected route; it is not a
count of SDK PDA internals, Pool hashing, all possible error paths, or a final
QV theorem. The P3 native counter recorded 583 raw calls and 452 exact distinct
concatenated inputs for one saved proof/public pair only; see
[`hash-input-counter-p3-20261014`](../evidence/hash-input-counter-p3-20261014/README.md).

## Probe entry and lifecycle dispatch

With `pool-adapter` enabled, `process_r1_cost_probe_instruction` admits only
first bytes 4/5/6, exact stage-one tags `[3,10]` or `[3,11]`, or the `ASQ8`
request prefix (`lib.rs:29–37`). Everything else returns
`InvalidInstructionData` before reading account contents. The old `[1,k]` and
`[2]` implementation is under `cfg(not(feature = "pool-adapter"))`
(`lib.rs:39–61`); it is not this build's route. In particular, that legacy
branch's additional checkpoint checksum hash at `lib.rs:51–52` is not reached
under the selected pool-adapter feature.

`r1_pool_adapter::process` dispatches 4 to init, 5 to prefix write, 6 to
finalize, `[3,10]/[3,11]` to stage 1, and other admitted data to stage 2
(`r1_pool_adapter.rs:982–993`). Lifecycle functions `lifecycle_init`,
`lifecycle_write`, and `lifecycle_finalize` (`:277–361`) contain no
`HashFn`, `find_program_address`, or CPI call. They validate instruction shape,
account authority/header/body, copy the body prefix, and clear the authority
on finalization. Malformed instructions fail before account borrows in each
handler. `lifecycle_accounts` checks account count, aliases, ownership,
privileges, signer, and nonzero authority (`:181–205`).

## Stage 1 and stage 2 verifier callback path

Stage 1 accepts only `[3,10]` or `[3,11]` and two accounts (`r1_pool_adapter.rs:868–884`).
It checks lifecycle/public framing and the candidate afterstate, exact proof
length, S2 tag, and zero checkpoint tail before hashing (`:886–928`). It calls
`super::first` (`:929`), which decodes the public statement and calls
`verifier::tx1` with `|p| hashv(p).to_bytes()` (`lib.rs:24–27`). The allowed
`k` split is 10 or 11 from the instruction byte. `tx1` rejects `k > 22`, parses
the proof before hashing, verifies the semantic prefix, prepares the query
state, and processes queries while `a.next < k` (`verifier.rs:342–350`). A
later semantic rejection may follow earlier transcript hashes; an invalid
proof shape is rejected before the first verifier hash. On success,
`checkpoint` hashes the proof, public bytes, and checkpoint checksum prefix
(`verifier.rs:297–316`).

Stage 2 first checks six accounts and the `ASQ8` magic (`r1_pool_adapter.rs:940–947`),
then `validate_asq8` authenticates the request/accounts and scans the ASPU
proof body (`:808–865,948`). Before `tx2_authenticated`, it checks exact proof
account length, reconstructs and length-checks the encoded public statement
(`:949–969`). It supplies the same `hashv` callback at `:970–977`.
`tx2_authenticated` uses `View::parse_shape`, `resume`, and
`while a.next < 22` (`verifier.rs:380–388`). `resume` rejects checkpoint
length/header/flags before digest work, then hashes the proof, public bytes,
and unkeyed checkpoint checksum prefix (`:325–339`); these are the three
repeated checkpoint input strings already identified by the raw-count note.
The authenticated path intentionally does not repeat the strict field
canonical scan (`verifier.rs:368–378`).

Per-query Merkle work in `query_with_geometry` hashes two private leaves,
checks their paths, and for S2 hashes one folded leaf/path if earlier paths
pass (`verifier.rs:242–263`). `merkle_path` has six levels (`:120–128`). The
source loop bound is 22 queries; a complete successful S2 query contributes at
most 21 Merkle leaf/parent hashes, while a rejecting path may stop early. The
query transcript draws eight squeeze/advance pairs once at row 31 in
`Transcript::queries` (`transcript.rs:35–45`), not eight pairs per query.

## Adapter PDA derivations on ASQ8

These are direct `Pubkey::find_program_address` call sites, separate from the
verifier callback:

- `authenticate_asq8_accounts` derives the master, checkpoint, and lane PDAs
  (`r1_pool_adapter.rs:615–667`): three direct calls on a path that reaches
  those checks.
- `authenticate_invariant_release_registry` derives either the legacy
  registry and entry (two calls, `:538–565`) or, when immutable-deployment is
  enabled, registry-v2, registry ProgramData, entry-v2, and verifier ProgramData
  (four calls, `:477–521`). The immutable-registry policy precondition is
  checked before this branch (`:465–478`).

Thus the adapter has five or seven direct PDA derivation sites on the
corresponding successful auth branch. `Pubkey::find_program_address` performs
SDK bump-search/hash work internally; the source call sites do not reveal a
fixed number of underlying SHA attempts. These PDA inputs are not passed to the
R1 `HashFn` callback.

## Pool ASQ8 terminal settlement closure

The Pool top-level `process_instruction` routes `ASQ8` to
`process_pair_forest_terminal_v1` (`processor.rs:2292–2373`). Before verifier
CPI, the pair-forest terminal code decodes/authenticates the request, master,
checkpoint, lane, current/root-history page, registry selection, nullifier
marker plan, payer/system accounts, and optional withdrawal transfer plan
(`pair_forest.rs:1384–1474`; `pair_forest_dispatch.rs:85–150,220–238`). The
relevant Pool PDA sites are:

- Master, retained checkpoint, and lane derivation in the account decoders
  (`pair_forest.rs:204–238,320–389,1191–1237`), plus another lane-address
  check in request/account validation (`:1096–1144`).
- Root-history page derivation (`history.rs:32–40,79–87`), reached from
  `validate_lane_current_page` or the fresh/rollover page branch in
  `plan_pair_forest_spend_layout_v1` (`pair_forest.rs:635–660,1024–1062`). A
  rollover plan can validate both current and next page addresses; the branch
  is state-dependent.
- Nullifier marker derivation checks its canonical digest encoding and then
  calls `find_program_address` (`nullifier.rs:25–39,85–96`). Terminal planning
  calls it once before verifier CPI; `create_nullifier_marker_if_needed_v1`
  re-plans/rechecks it after optional creation (`pair_forest.rs:1452–1478`,
  `processor.rs:1505–1545`).
- Pool-side verifier registry selection uses two direct derivations for the
  v1 registry/entry or four for v2 registry/entry plus both ProgramData PDAs
  (`registry.rs:165–310`). The verifier adapter separately performs its own
  registry/account authentication as listed above.

Pool terminal settlement itself has no direct `HashFn` call in
`pair_forest.rs` or `pair_forest_dispatch.rs`; the verifier CPI reaches the
adapter callback path above. Its CPI sites are distinct from SHA calls:
`dispatch_pair_forest_terminal_readonly_v1` invokes the verifier once
(`pair_forest_dispatch.rs:220–279`). Marker preparation may issue no System
CPI for an already program-owned zeroed marker, one `create_account` CPI for a
zero-lamport System-owned marker, or two/three CPIs for a funded System-owned
marker (`processor.rs:300–372,1505–1535`): the latter branch can transfer a
lamport deficit, then allocate and assign. A withdrawal adds one
`invoke_signed` token transfer after verifier success (`pair_forest.rs:1532–1542`);
private transfer has no token CPI. Failed validation/error returns before later
calls; Solana transaction rollback handles state writes after CPI failure.

## Separate prepared-settlement APIs

The Pool also contains a distinct prepare/settle/cancel workflow. It supplies
`solana_sha256` (`processor.rs:190–192`) as a `HashFn` to prepared-settlement
code (`:1092–1408,1409–1503,1554–1790`). This is not a direct call in the
ASQ8 pair-forest terminal function above. Its visible digest sites include
statement and receipt authentication, exact source Pool/page/receipt images,
optional next-page image, and prepared-plan/shard images. The format layer
hashes rollover/core digest-domain inputs on encode/decode
(`prepared_settlement_format.rs:256–258,357–361,503–507,549–554,599–605`);
`prepared_settlement.rs` also rechecks image digests when building/applying
plans (`:295–356,593–616,908–935`). Plan/shard PDA derivation is in
`prepared_settlement_format.rs:225–254`; their caller-path loops/account
branches are in `processor.rs:1092–1408,1554–1790`. The direct-SHA and PDA
families above are listed to avoid conflating this workflow with the tested
ASQ8 route; no aggregate count is assigned here.

## CPI inventory boundaries

The Pool `PoolCpiRuntimeV1` wraps `program::invoke` and
`program::invoke_signed` (`processor.rs:145–174`). In the terminal route the
verifier CPI is in `pair_forest_dispatch.rs:279`, optional marker creation
CPIs in `processor.rs:300–372`, and withdrawal token CPI in
`pair_forest.rs:1541`. These occur in the Pool program, not inside the R1
verifier adapter. `program::set_return_data` is not a CPI. Lifecycle 4/5/6
adapter routes perform no CPI. Other Pool instructions (initialization,
deposit, prepared-plan preparation/cancel, and prepared settlement) have
additional PDA/CPI/hash sites in `processor.rs`, `pair_forest.rs`,
`registry.rs`, `nullifier.rs`, and `prepared_settlement*`; they are not
summed with an ASQ8 terminal transaction here.

## Reuse and remaining accounting boundary

`QUERY-CALL-INVENTORY.md`, `J1-HASH-INPUT-LENGTH-INVENTORY-20261015.md`, and
`J1-ENTRYPOINT-SCOPE-DECISION-20261015.md` are the retained sources for the
R1 callback counts, exact input widths, and requirement not to omit PDA hashes
from any eventual shared-oracle model. This inventory adds the adapter auth,
Pool registry/page/nullifier PDA, Pool verifier/System/token CPI, and separate
prepared-settlement hash interfaces. It intentionally leaves those event
families distinct; a final all-program oracle/query bound must account for the
actual selected call graph, SDK bump search, Pool instruction sequence, and
error short-circuiting.
