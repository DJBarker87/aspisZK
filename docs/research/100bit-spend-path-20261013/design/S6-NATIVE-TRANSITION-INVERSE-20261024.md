# S6 original native transition inverse

2026-10-24. Extends S6-NATIVE-TRANSITION-DECODER-20261024.md. The native
transition inverse listed there as open is now proved. Whole S6 remains OPEN.

## Exact statement and premise removal

`AspisS6NativeLateCodec.accepted_inverse` states:

    for all bytes, statement,
      native_decode(bytes) = ok(RustOk(statement)) ->
      for all output, output.length = 1520 ->
      exists updated,
        native_encode(statement, output) = ok(RustOk(()), updated) and
        updated.val = bytes.val

These are the original extracted
`AspisR1TerminalDecoder.pool_v1.pair_tree_profile.decode_pool_v1_pair_late_public_statement_boxed_v1`
and `encode_pool_v1_pair_late_public_statement_v1`. Complete native snapshot,
afterstate and transition carriers are retained, together with actual mutable
slice operations, validators, checked index and child calls. The output buffer
is arbitrary apart from its API-required allocation size. Child and encoder
success, canonicality, header acceptance and index consistency are derived.
There is no Ops parameter, source-association hypothesis or hidden carrier port.

The prior enclosing encoder theorem concluded existence of a successful result
and its length. This theorem strengthens that result to exact byte equality,
using the same sole decode premise and output-size condition. The separate
two-success `accepted_roundtrip` helper retains encoder success, but the final
`accepted_inverse` derives it. No new quantifier restriction is introduced.
This is ACCEPTED-ONLY inverse correspondence. Previously checked native decoder
and encoder TOTAL results remain valid for all inputs and all rejection paths.

## Composition and validation

The encoder's complete accepted native body is checked against exact native
child contracts. The resulting source call graphs identify the actual snapshot
output and afterstate array. Their existing native inverses recover the original
payload bytes. Symbolic header and payload write lemmas compose all 1520 bytes,
including reserved zeros, and the decoder header frames telescope to the same
32-byte header. No concrete 1520-byte buffer or recurrence is normalized.

Accepted sources/receipts: s6-native-late-inverse-targets.json. Selected imports
and tools: matching -import-pins.json and -tool-pins.json. These files are under
evidence/s126-current-caller-20261021. All 6 changed targets exit0,
sum focused wall 84.561s, peak RSS
3281715200 bytes, zero swaps. Each receipt records
source revision/hash, exact target/command, Lean/lake and import/object hashes,
exit, wall, RSS, swap and printed axioms. Standard propext, Classical.choice and
Quot.sound only. Local jobs use the shared atomic lock, -j1 -M4400 and warm
imports. No heavy job, source adoption or unchanged full replay ran. Source-only
packet: no binaries or compiled objects.

Header-writes v1 had invalid multiline field syntax, corrected in v2. Encoder
contents v1 exposed the normal-case source graph; v2 composes its exact payloads
with named symbolic write lemmas. Failed diagnostic sources/logs are retained
but excluded, including error-recovery axiom reports. No resource options or
custom axioms were introduced.

Source pins are inherited unchanged from s6-native-late-source-pins.json:
original extraction0626294e34632812accf4cb14704f027368ea871, historical
freeze25866ec331cc7ce27dd9956609c11d32fa8fa58a, and the recorded research
inspection. Five relevant statement/arithmetic files are byte-equal. Current
owned-adapter/H5 caller and release artifact binding are not inferred from that
component equality. No production Rust or verifier changed.

## Remaining enclosing obligations

Native afterstate688, snapshot800 and transition1520 source inverse components
now exist. Next is the complete outer1880 forest
codec: connect the existing original outer encoder extraction and its full
nominal carriers/callee bindings, then prove its complete inverse. It is absent
from the legacy decoder extraction, so no manually invented native encoder or
assumed association suffices.

The final first/first_decoded/adapter stage1 theorem must instantiate the
complete FullForestAcceptedRoundtrip and actual current caller semantics,
including full statement/public/proof slices, S1 preparation/challenge provenance,
backend ports, state/ownership/capacity, errors, allocation/abort, ordered reads
and release observer None. S1 complete native preparation and caller connection
remain open. S2 remains transferred. The target is not yet established.
Any future source candidate adoption requires explicit equivalence and fresh
current source/tool/artifact re-pins; this unchanged component requires no
protocol/source decision.

## Subsequent TOTAL result, 2026-10-24

S6-OUTER-NATIVE-TOTAL-20261024.md now proves the concrete installed outer source
encoder TOTAL on every full native statement, without child-success premises.
This supersedes the earlier open TOTAL status above. Outer byte inverse and
actual SDK/caller binding remain open.
