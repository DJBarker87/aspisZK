# S6 native216 payment decoder totality and exact inverses

2026-10-24. Both original native payment codec components are now proved.
Outer1880 inverse and actual SDK/caller binding remain OPEN; S6 is not closed.

## Exact source claims

`AspisS6NativePaymentDecode.transfer_total` and `withdrawal_total` prove TOTAL
for the original native decoders on every Slice U8: a Rust result is returned
without Aeneas fail/div, including wrong lengths/headers, noncanonical fields,
invalid bindings, amounts and validation errors. No input or child-success
premise is retained. Common decode/header and complete field provenance are
checked against the original native functions and complete native records.

`AspisS6NativePaymentContents.transfer_accepted_inverse` and
`withdrawal_accepted_inverse` each have exactly one premise:

    native_decode(bytes) = ok(RustOk(full_native_payment))

Each conclusion is:

    exists encoded : Array U8 216,
      encoded.val = bytes.val and
      native_encode(full_native_payment) = ok(RustOk(encoded))

The actual functions are under
AspisR1TerminalDecoder.pool_v1.payment_relation, with names
decode/encode_pool_v1_private_transfer_public_v1 and
 decode/encode_pool_v1_withdrawal_public_v1. No independent header,
canonicality, common-field binding, digest success, validator success or whole
encoder success is assumed. All derive from that actual decoder execution.
The source common writer's byte7 remains initialized zero; no extra source
write is invented. All bindings, amounts/fee, destination/recipient, nullifier,
asset id, anchor fields and change commitment bytes participate.

Two-success helper forms in S6NativePaymentRoundtripV1 consume actual native
encoder returns for parent composition; the final inverses above derive those
returns. The inverse statements are ACCEPTED-ONLY; decoder TOTAL and the prior
native encoder TOTAL theorems cover all input/error paths independently.

## Reuse and source correspondence

The materializer migrates the existing checked payment proof patterns to the
original native function namespace and full native record types, then each
new target is kernel checked independently. It copies proofs and mathematical
byte formulas, not Rust or function implementations. Generic byte inverses,
write/frame composition, zero-word facts and native digest proofs are reused.

The first common-frame attempt exposed that an imported digest contract stated
the equivalent reference encoder return. The final proof uses the existing
unconditional full Result equality
AspisS6NativeDigestEncodeSourceEq.encode_eq to recover the actual native encoder
endpoint. Encoder write proofs use the actual native digest source contract.
No native/source association is assumed merely from matching names, byte widths
or accepted fixtures, and no simplified payment carrier is introduced.

materialize-native-payment-proofs.py --check pins every reused proof source,
the generated native proof source and the explicit namespace/equality changes.
All native functions themselves remain unchanged. Source pins compare four
whole Rust payment/atomic/field/format files across original extraction
0626294e34632812accf4cb14704f027368ea871, historical freeze
25866ec331cc7ce27dd9956609c11d32fa8fa58a and inspected research
b797d6d360b460b527c046e37dad1106e8beeabc. VALUE_LIMIT and POOL_V1_LEAF_CAPACITY are
separately compared as exact constant spans in their files with other changes.
These component pins do not re-pin the current SDK or release binaries.

## Validation and exclusions

s6-native-payment-codec-targets.json selects 11 changed targets, all exit0;
matching -import-pins.json, -tool-pins.json, source pins, proof-reuse metadata and
per-attempt receipts are under evidence/s126-current-caller-20261021. Exact
source revision/hash, target/command, tool/import/object hashes, exit, wall,
RSS, swap and complete axiom output are recorded. Sum focused wall
168.549s; peak RSS
3318513664 bytes; zero swaps. Thirty printed axiom
reports use only standard propext, Classical.choice and Quot.sound.

Jobs ran sequentially under the shared atomic lock, -j1 -M4400 with warm caches.
No unchanged full replay, resource override, custom axiom, native_decide, heavy
job or source adoption. This packet distributes source only, not binaries or
compiled objects. Decode helpers v1 was superseded by v2 adding full individual
map-helper axiom output before dependent compilation. Common decode v1's
reference/native endpoint mismatch is retained and excluded; v2 applies the
proved encoder equality. All final source versions are independently checked.

## Remaining enclosing obligations

The native216 inverses can now compose with the native snapshot800,
afterstate688 and transition1520 inverses and the concrete installed outer
encoder (already TOTAL) to prove FullForestAcceptedRoundtrip1880. Its full
outer decoder/body/header and exact1880 byte composition still need checking.

Then connect the actual current first/first_decoded/adapter stage1 source to
the same complete decoded statement and original public/proof slices, with S1
preparation/challenge provenance, backend ports, checkpoint, ownership/capacity,
state/errors, allocation/abort, ordered reads and release observer None.
S1 whole native preparation and actual caller correspondence remain open. S2
remains transferred and no other sessions' tracks changed. Target not yet
established. Any candidate adoption requires equivalence and fresh authoritative
source/tool/artifact re-pins; no Rust/source decision is needed for this
unchanged component proof.
