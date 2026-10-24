# Complete outer1880 native codec inverse, 2026-10-24

Status: checked ACCEPTED-ONLY inverse on the concrete original outer encoder
source cut and original native decoder. S6 current SDK/caller binding remains
OPEN. S1 whole preparation/caller remains OPEN; S2 ownership is transferred.
The overall <=2^-100 per-attempt target is not yet established.

## Enclosing claim and premise removal

`S6OuterNativeCodecV1.lean`, namespace `AspisS6OuterNativeCodec`:

```
accepted_inverse (bytes : Slice U8) (statement : NativeFullStatement)
  (accepted : nativeOuterDecoder bytes = ok (.Ok statement)) :
  ∃ encoded : Array U8 1880#usize,
    AspisS6OuterNativeInstalled.encode statement = ok (.Ok encoded) ∧
    encoded.val = bytes.val
```

This preserves the arbitrary input slice, complete original native statement,
actual decoder acceptance event and complete byte equality. Both private
transfer and withdrawal are proved. The sole input premise is that same
original decoder acceptance. No separate native validator, child decoder,
child encoder, source selector, canonicality, successful continuation, length,
or output layout premise remains. `accepted_roundtrip` additionally provides
the two-success interface, using deterministic equality with that same encoder.

Before: concrete `encode_total` proved an arbitrary native statement yields
some Rust Result, including format errors. Exact transition/payment inverses
and accepted outer frames were separate. After: the enclosing actual accepted
outer decode guarantees successful concrete outer encoding AND equality of all
1,880 bytes. Child success and contents are derived from its reached slices.
This does not merely bundle independent premises into a structure.

`S6OuterAcceptedCalleesV1` derives concrete installed validation, transition
and payment calls from accepted outer decode. `S6OuterEncodeSuccessV1` checks
both original source writer branches and all reached buffer/index/cast bounds;
`S6OuterEncodeFromDecodeV1.encode_success` discharges their readiness premises.
`S6OuterEncoderContentsV1` retains the actual installed child returns and
complete encoder byte layout. `S6OuterAcceptedByteJoinV1` connects those same
calls, by deterministic equality, to the accepted original common144 prefix,
transition1520 slice144..1664 and payment216 suffix1664..1880. The final theorem
composes these with slice recomposition.

`S6OuterWriteFramesV1` and `S6OuterByteLayoutV1` prove symbolic writer frames;
the kernel never needs to unfold a concrete 1,880-byte recurrence/buffer.
No Rust source, production verifier, protocol or extraction was changed.

## Exact source boundary and remaining trust

`AspisS6OuterNativeInstalled.encode` is the previously checked concrete instance
of the separately extracted original outer encoder source cut. Its five child
operations are installed to the original native source functions, with complete
native/cut carrier bijections and error transport. It has no free Ops argument.
The legacy native decoder extraction does NOT contain an outer encoder, and
this work does not invent or claim one. The existing source-cut/extraction TCB
and exact source pins are reused, without a new native-association assumption.

The source-only packet pins the existing outer binding, native outer decoder,
parent, payment and transition source packets. These record original extraction
0626294e34632812accf4cb14704f027368ea871, historical freeze
25866ec331cc7ce27dd9956609c11d32fa8fa58a and inspected research source spans.
Unchanged selected functions do not establish whole current forest-file or
owned adapter/H5 artifact equivalence. No new source freeze is declared here.
Current release pins remain default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4
and devnet 63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299
per the authoritative session A handoff; no adoption/re-pin is inferred.

The remaining `S2Y_ForestPublic.FullForestAcceptedRoundtrip ops` interface uses
CURRENT owned operation carriers and installed `ops.op47` decoder/`ops.op22`
encoder. This native theorem supplies its full mathematical/source codec law;
concrete current operation/carrier installation is still required. No arbitrary
Ops instance or callback chosen to match was asserted. Also open are complete
stateful `FullForestPublicPort` and `ComposedFirstPort/Value`: Box/Vec owners,
capacity/allocator/abort trace, error mapping and ordered effects, and the same
full statement/public/proof through first/first_decoded/stage1 with release None.
S1 preparation/transcript/gamma scratch and resumed powers must be joined at
the actual current call sites. Other sessions' backend tracks are untouched.

## Validation

Eight focused changed targets passed, sequentially under the atomic local lock,
-j1 -M4400, using pinned warm imports. Exact commands, source revision/hashes,
source copies, exit0, wall, RSS, swaps and #print axioms are in the selected
receipts. Sum focused wall: 99.624 seconds. Peak RSS: 3,385,720,832 bytes.
Zero swaps. Thirty-one axiom reports contain only propext, Classical.choice and
Quot.sound. This is focused cached compilation, not a coherent release replay.
No unchanged full replay, heavy job, custom axiom, sorry, native_decide or
resource-option override was used in accepted source.

Packet: evidence/s126-current-caller-20261021/s6-outer-native-codec-{targets,
source-pins,tool-pins,import-pins}.json. Audit tool:
`tools/s6-full-forest-roundtrip-20261023/check-outer-native-codec.py`.
Source-only evidence, no binaries/compiled objects distributed.

Excluded diagnostic attempts remain separately recorded: initial writer proofs
left impossible Rust error branches; explicit positive map and branch facts
eliminate them. Contents attempts exposed run-equality rewrites, Array namespace
ambiguity and a reducible-header comparison hitting recursion depth. The fix
uses the named symbolic layout with its header explicitly unfolded before
application; no resource limit was raised. Byte-join attempts needed explicit
unfolding of the two separately extracted constant namespaces. Final inverse
attempts needed explicit tag and prefix-alias normalization. None was rerun
unchanged. Failed compiler recovery sorryAx reports are excluded from accepted
targets. Initial packet bookkeeping referenced a nonexistent payment pin name;
it was corrected to the existing s6-native-payment-source-pins.json before audit.
