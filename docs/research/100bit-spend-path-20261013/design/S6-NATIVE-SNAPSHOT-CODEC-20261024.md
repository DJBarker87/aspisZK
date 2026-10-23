# S6 original native snapshot codec inverse

2026-10-24. This extends S6-NATIVE-SNAPSHOT-DECODER-20261024.md: its remaining
snapshot inverse obligation is now discharged at the native codec component.
The enclosing S6 caller theorem remains OPEN.

## Exact premise removal

`AspisS6NativeSnapshotCodec.accepted_roundtrip` proves:

    for all bytes, snapshot, output, updated,
      native_decode(bytes) = ok(RustOk(snapshot)) ->
      native_encode(snapshot, output) = ok(RustOk(()), updated) ->
      updated.val = bytes.val

`AspisS6NativeSnapshotCodec.accepted_inverse` strengthens this to:

    for all bytes, snapshot,
      native_decode(bytes) = ok(RustOk(snapshot)) ->
      for all output, output.length = 800 ->
      exists updated,
        native_encode(snapshot, output) = ok(RustOk(()), updated) and
        updated.val = bytes.val

These are the actual original extracted functions
`AspisR1TerminalDecoder.pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1`
and `encode_pool_v1_pair_live_snapshot_v1`, using their complete native record,
errors, mutable output slice and native iterator loop. No Ops callback or
simplified carrier is introduced. Decoder acceptance is the sole input premise.
An 800-byte output allocation is required by the actual encoder API; every such
buffer is covered regardless of its initial contents. Validator, canonicality,
format-return, digest-encoder and whole-encoder success are derived, not assumed.
The newly existential updated buffer replaces an assumed successful encoding;
this is not packaging the old success premise in a structure.

The inverse is ACCEPTED-ONLY by its statement. The independent decoder totality
and encoder totality theorems cover arbitrary input slices/records/buffers and
all rejections; the inverse does not weaken those TOTAL results.

## Composition checked

The native encoder graph is proved by executing its original extracted body
against exact child contracts. The original frontier loop's output is joined
to its previously checked symbolic fold; the complete prefix writes and fold
are then composed into byte lists. No concrete 800-byte recurrence is reduced.
The decoder frames independently telescope to the same complete byte list.
Actual format function return equality identifies their format arrays.

Encoder success is derived from native validator success with the correctly
sized output. A small native Result branch graph retains the error branch's
connection to the input Result; a weaker existing branch postcondition omitted
that connection. The strengthened helper is proved by cases on the actual
Result, with no assumption added to the codec theorem.

## Evidence and limitations

Source freeze/extraction pins and current statement compatibility are inherited
from the decoder packet and s6-native-parent-total-source-pins.json. No Rust,
production verifier, extraction source or release artifact changed. Historical
native source revision remains 0626294e34632812accf4cb14704f027368ea871,
assessed against freeze 25866ec331cc7ce27dd9956609c11d32fa8fa58a.
Do not interpret this as binding a newer SDK or release binary.

New accepted receipts are selected by s6-native-snapshot-codec-targets.json;
selected transitive imports and script hashes are in the accompanying
-import-pins.json and -tool-pins.json under evidence/s126-current-caller-20261021.
The 6 changed targets exit 0, total wall 98.952s,
peak RSS 3281240064 bytes, zero swaps. Only standard
propext, Classical.choice and Quot.sound axioms appear. Each receipt records
exact target/source/tool/import pins, command, exit, wall, RSS, swap and axioms.
Local jobs ran sequentially under the shared atomic lock with -j1 -M4400.
Focused checks only; no unchanged full replay. Source-only packet; no binaries.

Diagnostic attempts are retained separately and excluded. Encoder graph v1
exceeded recursion depth in a broad simplification of the output buffer;
symbolic slice congruence replaces it in accepted v3. Prepare v1/v2 exposed
small numeric coercions and append association; v3 had a redundant tactic;
accepted v4 uses named chunk/length facts. Decoded layout v1 had a reversed
equality, fixed in v2. Encode success v1 exposed the weak branch contract,
fixed by the checked branch graph in v2. Codec v1 had eliminated-variable and
pair-projection elaboration errors; v2 is accepted. No resource overrides were
introduced. Failed elaboration axiom output is never accepted evidence.

## Remaining actual enclosing obligations

Native snapshot inverse is closed. Next: native 1520-byte transition inverse,
then the outer 1880-byte forest encoder's full-carrier/callee binding and inverse.
The actual first/first_decoded/adapter stage1 public reuse theorem still needs
that complete source codec law and installed caller correspondence, including
SDK state, ownership, errors, aborts, allocation, ordered reads and release
observer None. S1 complete native preparation/challenge execution and SDK
correspondence remain open. S2 remains with its transferred owner.

No protocol/source decision is required for this unchanged native component.
Adopting any candidate outside it requires explicit equivalence and fresh
source/artifact re-pins. Target not yet established.
