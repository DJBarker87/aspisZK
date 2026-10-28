# D371 input origin trace (source review; formal closure pending)

This review distinguishes the selected devnet proof-account route, its fixture
harness, the wallet adapter, and a direct Rust library caller. It does not
change `HonestInput` or withdraw D370. Source revision at review entry is
3197fab0ebe160020af494199a25b24940e179a8. Paths below refer to that revision;
the implementation files are unchanged during this review.

## Selected devnet route and JSON request

`tools/r1-cost-probe/src/bin/devnet_spend.rs:14` parses stdin as
`serde_json::Value`. An `action` dispatches to `plan::run`. The proving arm is
`devnet_spend/plan.rs:80–116`. Its only forest-compiler calls are at line 105.
`pv_client_gate.rs:708` builds the fixture harness's request.json with:
action, pool, mint, payer, registry, verifier, note, withdrawal, destination,
checkpoint, lane_bytes, checkpoint_bytes, proof_dir, proof_accounts,
public_account, verifier_checkpoint. **There is no recipient owner-key, salt,
input-note opening, value or asset-id field in this JSON ABI.** Adding such a
JSON member does not feed the compiler: the planner never reads it.

`note` is read with `as_u64().unwrap() as u32`. `note(n)` searches at most
10000 candidates using `digest(10+j)` and `digest(100+j)`. An unavailable
selection panics before compilation. Truncation of an oversized selector or
release wrapping in seed addition does not bypass the digest's final `% P`.
The fixture harness supplies 0 for transfer and 1 for withdrawal. No JSON
integer is converted directly into a recipient limb or a note value.

| Compiler input | Actual planner origin | Raw representation boundary |
|---|---|---|
| input.nullifier_key | `note(n).0`, `digest(10+j)` | Every lane is `M31((seed+17*i+1)%P)` |
| input.salt | `note(n).1`, `digest(100+j)` | Same generator |
| input.value | literal 1000 | Below VALUE_LIMIT and P |
| input.pair_leaf | `single_output(cm)` where cm hashes derived owner, value 1000, asset 77 and salt | Constructor sets occupancy/unused commitment/inverse; validates commitments |
| selected_second | literal false | Bool; compiler uses u32::from |
| membership.index | reconstructed fixture leaf position, cast to u32 | Full compiler rejects index >= 2^20 |
| 20 membership siblings | reconstruction of two fixture deposit leaves and `POOL_V1_PAIR_EMPTY_ROOTS` | Note/node hashes or pinned empty roots |
| 3 super-root siblings | reconstructed eight-lane root tree | Node hashes of the preceding roots |
| super-root directions | Boolean bits of input lane | Compiler converts Bool to 0/1 |
| recipient.owner_key | `derive_owner_key(&digest(300))` | Hash output; not parsed from recipient address or JSON |
| recipient.salt | `digest(400)` | Mod-P generator |
| recipient.value | literal 600 | Below VALUE_LIMIT and P; unused on withdrawal |
| change.owner_key | `derive_owner_key(&digest(500+n))` | Hash output |
| change.salt | `digest(600+n)` | Mod-P generator |
| change.value | 400 transfer / 750 withdrawal | Literals below VALUE_LIMIT and P |
| public.nullifier | `pool_v1_nullifier(&k,&salt)` | Hash output |
| public.recipient_commitment / change_commitment | `pool_v1_note_commitment` from the above generated openings | Hash outputs |
| public.asset_id; context.asset_id | literal M31(77) | Canonical literal |
| public.anchor_root; context.anchor_root | decoded checkpoint.global_root | Checkpoint account codec calls `decode_digest_canonical` |
| pool, deployment_domain | master PDA bytes; literal [5;32] | Byte arrays, not raw M31 tuple constructors |
| anchor_sequence | checkpoint.checkpoint_sequence | u64 metadata, not an M31 limb |
| withdrawal.amount | literal 250 | Below VALUE_LIMIT and P |
| withdrawal.destination_token_account | `Pubkey::from_str(q["destination"])?.to_bytes()` (unwrap in helper) | 32 address bytes, not a recipient M31 owner key |
| context.spent_nullifiers | empty slice | No externally supplied limbs |
| snapshot.pool, deployment_domain | master PDA bytes; [5;32] | Byte arrays |
| snapshot.sequence, next_pair_index | lane.tree.next_leaf_index | u64 index; codec/tree validation bounds it |
| snapshot.current_root, frontier | decoded lane.tree.root/frontier | Incremental tree account codec decodes canonical digests |
| empty-root table, round constants, domain tags | pinned statement/refine source constants | Constant range audit required, not JSON data |

`lane_bytes` and `checkpoint_bytes` pass through the hex-to-byte routine and
then the actual account decoders before their fields enter the compiler.
Malformed hex may panic; it does not construct an unchecked M31. Lane decode
delegates to `IncrementalMerkleTreeV1::decode_with_empty_roots`; checkpoint
decode calls `decode_digest_canonical` for global_root. Account master and
lane identity checks precede compilation. These account decoders must not be
confused with D370's different, 800-byte live-snapshot codec; both require
their own source association.

## RealR1_client and failure visibility

`crates/aspis-r1-cost-probe/src/RealR1_client.rs:20` accepts an already compiled
`PoolV1PairForestMergedC1CompilationV1` and semantic public view. It has no
request decoder or forest compiler. It forwards them unchanged to
`prove_masked_retrying_with`, Variant::S2, with OS-generated attempt secrets
and retained proof-account public keys as nonces. The planner is the selected
operational caller. Other occurrences are tests/diagnostics, not an additional
JSON witness ABI.

A direct Rust caller can construct public `M31(pub u32)` and witness structs
with raw P, compile them and call this API: this is the D370 library path. It
does not establish that the selected planner obtains such a representation.
The concrete D370 rejecting guard is decided by the recipient key's raw
representation, before helper challenges; it does not reveal a sender secret
in that fixed counterexample. On that path the caller receives Semantic,
and the planner's `?` would return before proof files and terminal instruction
construction. No successful spend/transaction is claimed for the bad input.

## Separate wallet adapter and address codecs

`crates/aspis-pool-wallet-v1/src/live_pool_witness_adapter_v2.rs:329` constructs
output witnesses by `decode_digest_canonical(note.owner_key())` and
`decode_digest_canonical(note.salt())`; failures return NoteOpening. Input
construction at 384–480 decodes both pair commitments, every membership
sibling, every checkpoint lane root, the nullifier, nullifier key and input
salt. It checks derived owner equality against a decoded owner. Super-root
siblings are generated from decoded roots with `pool_v1_tree_parent`.
The `NoteOpeningV1::new` boundary also validates owner/salt byte canonicality,
value < VALUE_LIMIT and asset_id < P (`lib.rs:390–413`). The adapter repeats
the digest decoding even for an existing opening.

This adapter is not called by `devnet_spend/plan.rs`; it must not be used to
silently add a decoder to that planner or to the generic RealR1_client API.
Solana public-key/base58 codecs provide account addresses as bytes. They do
not decode an Aspis recipient's eight M31 owner-key limbs on the selected
route. No raw noncanonical recipient-key path has been identified in the
selected JSON route by this source review.

## Evidence boundary

50303 proves the extracted scalar decoder's complete Option result, success
range for arbitrary bytes and rejection of encoded P. Digest success
reflection, script-checked body association, finite native validation,
generator/hash ranges and compiler/mask preservation are separate obligations.
This document is not yet a completed structural (K-1 substitute) proof of the
entire route or N3. In particular, a source inspection of `%P` or a hash's
reduced final layer is not being reported as a universal compiled theorem.


## D371 proof status at focused-budget exhaustion

No raw noncanonical private/statement limb source was found in the selected
JSON planner. The only raw M31 constructors left after its final-remainder
generator are literal 77. The four output owner/salt origins are supplied by
`PV_L2C_PlannerOutputs.outputs`, with unconditional hash success and range for
those generated keys. Canonical scalar/digest decoder laws retain rejecting
branches. The ordered account cut proves all root/frontier fields are decoded,
including active frontier slots; `AccountOrigins` and `AccountEncode` connect
the exact returned positions and lossless bytes. The generic Rust API still
accepts compiled columns without imposing this route: D370 is retained.

`ClientRoute.Transfer/Withdrawal` explicitly includes successful outer compile,
asset 77, ordered account field-decode provenance and output origins. It uses
the planner's directly constructed snapshot, not the different 800-byte codec.
`transfer_columns`/`withdrawal_columns` derive shape 16 x 1024 and every raw
cell < P through exact recorded fields, all block pre/absorption/permutation
rows, path/value/occupancy rows, banks, merge and returned compiler columns.
No N3 success or raw-column bound is part of the input carrier.

`MaterialN3.transfer/withdrawal` proves the complete owned base,d,g guard cut
returns Ok from stateful sampler/build/apply executions. These execution
records retain sample states/results and assume no column canonicality or
guard outcome. Instantiating them from the *whole native* material/derive/
clone caller remains P, as does the exact selected-planner-to-carrier domain
inclusion beyond the source-checked field cuts. This is not an unconditional
whole-native N3 or deployed observation theorem. The source binding receipt
names these remaining links explicitly; no new trust item hides them.

Both original fixtures satisfy the canonical-origin refinement of the old
honest family, with successful lossless digest/account-field decoder witnesses.
That broader refinement is not asserted equal to the selected planner's
specific two-deposit reconstruction. The native two-case diagnostic uses
generated output fields and real account codecs and both full provers pass;
it is finite validation, not exact planner non-vacuity or universal privacy.
