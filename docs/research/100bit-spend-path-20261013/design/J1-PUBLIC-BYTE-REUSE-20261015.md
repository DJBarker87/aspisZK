# J1 public-byte and Pool-constructor reuse inventory

Inspection base: `c7b5a949e2274b15ac91a6299fbbc3da691aeb3c`. This is a
source map only. It does not establish that the Rust parsers refine the Lean
public model or close J1.

## Current source path

The cost-probe entrypoint's `first` function decodes the 1,880-byte ASF8
statement, selects `Public::Transfer(public, &common.lane_transition)` or
`Public::Withdrawal(...)`, then passes that value and the original bytes to
`verifier::tx1` (`programs/r1-cost-probe/src/lib.rs:24-27`, SHA-256
`294546036e6cf8bb8dcc1f1f4a65c5e0887ac04593cdda801f58c75a284d582a`). The
Pool adapter's `decode_public_statement_box` calls the same ASF8 decoder on
the public account body (`programs/r1-cost-probe/src/r1_pool_adapter.rs:171-177`,
SHA-256 `b2adab8610189a5031fc6f28a7cdeef12c01aa292423743cb4696aa3ee1590a4`).
Its stage-one path validates that decoded statement and calls `super::first`
with the body (`:886-897`); stage two reconstructs ASF8 bytes from the
validated ASQ8 payment object and then calls the authenticated verifier
(`:929` and following). The verifier's ASQ8-to-statement reconstruction is a
separate path in `programs/aspis-verifier/src/v7_pair_forest_dispatch.rs`;
its ASF8 decoder is under audit/test configuration rather than evidence of
an additional production decode call.

The outer ASF8 encoding has magic `ASF8`, version 1, a transition-kind byte,
and digest-encoding version at bytes 0–6; exact total length is 1,880. It is
144 common/header bytes, a 1,520-byte late-transition record, then a 216-byte
payment record. The late record starts at 144 and payment at 1,664. The ASF8
decoder checks total length, magic, version, kind, and digest encoding before
decoding both records and invoking the statement validator
(`crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs:29-50, 386-415`,
SHA-256 `becc01f162f23cd9b4a7fd3780be5a441c9b7265f3078282244cc938da63a16c`).
The common object carries master/checkpoint/lane account keys, output lane,
checkpoint sequence, historical global anchor, and the lane transition
(`:92-103`). Validation checks nonzero account bindings, lane range, and
cross-field bindings including pool/master, deployment, sequence, historical
anchor, and nullifier-derived output lane (`:227-270`).

The 216-byte payment portion has variant headers `ASCP` (private transfer)
and `ASWP` (withdrawal), version/kind/digest-version/reserved bytes in 0–7,
pool in 8–39, deployment domain 40–71, little-endian anchor sequence
72–79, canonical anchor digest 80–111, canonical nullifier 112–143, and
little-endian asset ID 144–147, required below M31 modulus P. Private transfer
requires zero fee/reserved bytes 148–151 and has canonical recipient digest
152–183 and change digest 184–215. Withdrawal instead stores little-endian
amount 148–151, destination account 152–183, and canonical change digest
184–215; validation requires `0 < amount < VALUE_LIMIT` and a nonzero
destination (`crates/aspis-statement/src/pool_v1/payment_relation.rs:28-43,
45-68, 182-245, 314-449`, SHA-256
`8b543d3de5aa29d1e510e8ca18bd2bc6dae6c405b7d6f97402c572dfdbab2588`).
The exact fixed-size decoders select the matching header and validate M31 and
digest encodings before returning typed payment structs.

The late record contains `PoolV1PairLiveSnapshotV1` (pool, deployment,
sequence, next pair index, current root, frontier) and a candidate afterstate
(`crates/aspis-statement/src/pool_v1/pair_tree_profile.rs:382-411`, SHA-256
`8a7a4c7bdd3fe0ecd14d6fc920182be434ab92536924de22d269d906be3387b2`). Its
validator requires sequence equal next-pair-index, index below capacity, and
canonical roots/frontier digests (`:443-463`); the statement validator also
requires the candidate index to advance by one (`:533-537`).

The semantic terminal's private-transfer constructor maps the payment fields
to `variant=PrivateTransfer`, `anchor=anchor_root`, `nullifier`, `asset_id`,
`recipient=some(recipient_commitment)`, `change=change_commitment`, and
`withdrawal_amount=none`; withdrawal maps `variant=Withdrawal`, recipient
none, and amount some. Both retain the transition reference
(`pair_forest_semantic_terminal.rs:87-98, 1312-1346`, SHA-256
`2bb7db64dc53c8a268e42b0fe46da64ab1afcb03d28bbec2569b2abc30cbc074`). The
semantic public byte serialization then emits, in order: variant byte (0 or
1), anchor's eight little-endian M31 limbs, nullifier's eight limbs, asset ID,
recipient-presence byte and optional eight limbs, change's eight limbs,
withdrawal-presence byte and optional amount limb, next-pair-index as
little-endian u64, live snapshot's 20 frontier digests, candidate next root,
and candidate next frontier's 20 digests (`:1998-2040`). Pool/deployment,
sequence, current root, and other account-level context are deliberately not
fields in this semantic byte view (`:1999-2001`).

## Existing Lean/Aeneas reuse and exact gap

`R0P.Core.Public` has the semantic fields `variant`, `anchor`, `nullifier`,
`assetId`, `recipient`, `change`, `withdrawalAmount`, `nextPairIndex`,
`snapshotFrontier`, `nextRoot`, and `nextFrontier`
(`docs/research/v8-r0-sem-proof-20261008/lean/R0P/Core.lean:50-66`, SHA-256
`eba6bb784803b5f00922724efc9997a8d5ab6bc55cd8c100bffd8a397dabe1f9`). This
matches the semantic serialization's field inventory. `PublicOptionShape`
provides an executable checker and `check_eq_true_iff`, plus constructors and
extractors for the two option shapes (SHA-256
`0fb33426084f3452a53dec73cf7c982e447a4c671e4bdf029807fbdc51232ae2`). It
only checks recipient/withdrawal-option presence and nonzero withdrawal
amount. It has no byte parser, tag check, M31 bound, digest canonicality,
amount upper bound, or binding to the Rust structs.

The generic `SpendRelationMap.rspend_map_iff` and
`SpendRelationMap.canonical_map_iff` transport an already-constructed public
and witness along an injective ring hom; they do not construct a public from
bytes (`SpendRelationMap.lean`, SHA-256
`8cf7bc8dc3c4c84ca68085595b18c23d9449bdd946f6c234b9e42b43e6a38030`).
`SpendRelationExtraction.of_production` consumes production/copy-link facts
and a shape premise and produces an existential `Rspend` witness; it does not
parse a Rust statement (SHA-256
`02125315e3db3fad9a05b63f69a8e9ab41e1fadc220d3716ec5df9de9854acd2`).
Repository searches found no Lean/Aeneas declaration for the current
`decode_pool_v1_pair_forest_terminal_statement_v1`, ASCP/ASWP parser, or a
byte-list-to-`R0P.Public` mapping. The retained historical
`AspisPool.V7EightLaneCompactDispatch` theorem proves equality of two abstract
reconstructions after authenticated state echoes; its module explicitly
leaves Rust byte equality and account parsing as source/runtime obligations
(`AspisFormal/AspisFormal/Pool/V7EightLaneCompactDispatch.lean:1-13, 105-123`,
SHA-256 `41bbb65b7eb6344801cea6659dc5eb5ec221c2141e07f85bffb1fbb0962b52ee`).
It is not a parser refinement result.

The smallest useful next statement is therefore conditional and explicit:
given success of the current typed ASF8 decoder, plus byte-decoder lemmas for
each nested payment/late record and the specified M31 embedding, construct
`pub : R0P.Public M31Exact` whose fields equal the projection above; then prove
`PublicOptionShape.canonical pub` from the selected typed variant and decoder
guards. The transition projection should map the live pair index/frontier
and candidate root/frontier into the four corresponding R0P fields. This
statement must include those state fields: proving only the 216-byte payment
projection would not yield a complete `R0P.Public`. No such source-to-model
theorem is present in the inspected reuse set, and the statement still needs
the byte-level decoder refinements before it can be discharged.
