# S6 original native snapshot decoder: totality and accepted byte frames

2026-10-24. Source-only focused-extractor-proof-packet-v1. Scope: native snapshot
codec component; S6 enclosing caller theorem remains OPEN.

## Claims established

`AspisS6NativeSnapshotDecodeTotal.decode_total` has no input premise:
for every actual `Slice U8`, the original extracted
`AspisR1TerminalDecoder.pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1`
returns `ok result`, including all Rust error paths. It cannot fail or diverge
in this extracted semantics.

`AspisS6NativeSnapshotDecodeTotal.accepted_frames` has exactly one premise:
the same actual native decoder returns `ok (RustOk snapshot)` on the supplied
bytes. Its conclusion gives the original full snapshot record's root and all
20 frontier digest chunks, pool, deployment domain, sequence and next index,
plus actual native validator success. The complete wire header is recovered:
800 bytes, original magic/version, seven reserved zero bytes, and a 32-byte
format array returned by the actual format-binding function. No separate
canonicality, parser acceptance, child success, buffer size or validator premise
is retained.

The intermediate `part*_frames` results require an 800-byte slice. That
premise is derived by the complete decoder, not retained by `accepted_frames`.
The decoder's full Result equality to the factored body is
`AspisS6NativeSnapshotDecoderFactored.decode_source`, quantified over all slices.
No free codec operations, replacement record, Rust edit or new extraction is
used. The packed read helpers contain the exact native cast/unwrap/decode calls.
The generator verifies textual re-expansion, and the kernel separately checks
packed-to-unpacked and unpacked-to-original full Result equality.

## Pins and validation

The imported native source remains the historical extraction from revision
0626294e34632812accf4cb14704f027368ea871, assessed against freeze
25866ec331cc7ce27dd9956609c11d32fa8fa58a. The unchanged relevant statement files
and current-source audit are recorded in `s6-native-parent-total-source-pins.json`;
this packet adds exact native source/function and generated-source hashes in
`s6-native-snapshot-decoder-factoring-v1.json`. This is component evidence,
not an assertion that a newer SDK or compiled release artifact is pinned.

Accepted targets/receipts: `s6-native-snapshot-decoder-targets.json`.
Selected transitive import closure: `s6-native-snapshot-decoder-import-pins.json`.
Scripts: `s6-native-snapshot-decoder-tool-pins.json`.
All paths above are under evidence/s126-current-caller-20261021.
Each receipt records exact source revision/hash, Lean/lake tool hashes, command,
exit, wall time, RSS, swap and printed axioms. All 13 targets exit 0,
sum focused wall time 195.217s,
maximum RSS 3305324544 bytes, zero swaps.
Only propext, Classical.choice and Quot.sound appear. Local jobs use the atomic
shared lock, -j1 and -M4400, with warm imports. No full unchanged replay ran.
No compiled objects are distributed.

## Failed approaches retained and excluded

Factoring v1 exceeded default recursion depth when reassociating the entire
body; replacement proves four-entry chunks then composes exact equalities.
Factoring v2 tried to unfold an absent helper; v3 is accepted.
Read-digest v1 used an inapplicable WP lemma form; v2 is accepted.
Decoded-frames v1 hit default automation limits with a hidden length constant;
v2 exposed the resulting bound goals. Replacement explicitly unfolds only the
length constant. V3 then left two small `take length` goals; named symbolic
array-length facts solve them in accepted v4. No resource options were raised.
Failed print-axioms output is excluded, including elaboration placeholders.

## Remaining enclosing obligations

This discharges native snapshot decoder totality and accepted byte frames.
It does NOT discharge native snapshot encode/decode inverse, transition inverse,
outer 1880-byte forest encoder correspondence/roundtrip, or the installed
`first`/`first_decoded`/adapter stage1 public reuse theorem. SDK account effects,
errors and release observer None must remain connected through their actual
caller boundary. S1 whole preparation/challenge execution and SDK correspondence
are still open. S2 remains transferred to its owner. Target not yet established.

Next consumer: native snapshot encoder byte composition, then its accepted
inverse, transition and outer forest composition. Any eventual source candidate
adoption needs explicit equivalence, current source freeze and release re-pins;
this packet does not modify or adopt production source.
