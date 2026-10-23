# S6 native transition: total decoder, accepted frames and encoder success

2026-10-24. Source-only focused-extractor-proof-packet-v1. The 1520-byte
transition's exact inverse remains OPEN; this packet does not close S6.

## Actual claims and exact premises

`AspisS6NativeLateDecodeTotal.decode_total` is TOTAL: for every actual Slice U8,
the original extracted `AspisR1TerminalDecoder.pool_v1.pair_tree_profile.decode_pool_v1_pair_late_public_statement_boxed_v1`
returns `ok result`, covering all Rust errors with no failure/divergence.
It does not assume a length, header, successful child or accepted input.

`AspisS6NativeLateDecodeTotal.accepted_frames` has only the actual native
successful decode as a premise. Its conclusion gives the complete 1520-byte
header (magic, version, item count, exact LE length fields 32/800/688/1520 and
reserved bytes24..31), two actual native child decode successes on exactly the
snapshot slice32..832 and afterstate suffix832..end, and the actual checked-add
relation between the complete native snapshot and candidate afterstate indices.
Both children use their original full native record types. No observer, SDK,
account or field is replaced by a simplified carrier.

`AspisS6NativeLateDecodeTotal.accepted_validity` derives both original native
validators and the index relation from the same decode premise. The generic
word16/word32 cast-frame lemmas prove that the source's usize comparisons retain
the full input words; no truncation, canonicality or independent range premise
is assumed. Fixed-width casts and 32+800 are discharged in the focused proofs.

`AspisS6NativeLateEncodeAccepted.encode_from_decode` then proves:

    for all bytes, statement,
      native_decode(bytes) = ok(RustOk(statement)) ->
      for all output, output.length = 1520 ->
      exists updated,
        native_encode(statement, output) = ok(RustOk(()), updated) and
        updated.length = 1520

The output buffer is arbitrary apart from the actual API's size requirement.
Independent snapshot success, afterstate success, child validator success and
index consistency are removed from this enclosing native encoder theorem.
They are derived from the one decode premise. The intermediate
`encode_valid_spec` retains the three explicit native validity facts; the
`encode_from_decode` theorem instantiates all three concretely.

This is ACCEPTED-ONLY encoder success, not the missing byte-equality law.
It does not conclude updated.val=bytes.val. The prior encoder TOTAL theorem
(S6NativeLateEncodeTotalV1) remains valid on arbitrary native records and buffers,
including rejection paths. Neither result implies the exact inverse alone.

## Source correspondence and resource handling

Four exact source cast/copy/unwrap sequences are grouped in named read helpers.
`AspisS6NativeLateDecoderFactored.decode_source` proves full Result equality to
the original decoder. `AspisS6NativeLateDecoderSplit.decode_source` further
factors its unchanged reserved-byte continuation, again with full Result
equality. Both generators check textual re-expansion; this check supplements,
and does not replace, the kernel equalities. All callees, native fields, errors,
branch order and input slices remain original. No Rust or production source
changes, source adoption, fresh extraction or new opaque replacement occurred.

Whole accepted-frame automation hit the default 200000-heartbeat limit. The
replacement checks header-word arithmetic and the reserved/child continuation
separately, then composes them. A dependent raw-array rewrite is handled by a
proved subtype equality; no buffer reduction, heartbeat/recursion override or
larger cap is used. Encoder success's broad simplifier also recursed into a
large buffer expression; explicit Result/ControlFlow contradiction proofs
replace it. The accepted source is pinned separately from failed diagnostics.

## Pins and checked evidence

Source: original extraction revision 0626294e34632812accf4cb14704f027368ea871,
historical source freeze 25866ec331cc7ce27dd9956609c11d32fa8fa58a. Five relevant
statement/arithmetic files are whole-file byte-equal at both and at inspected
research revision 8c770d76b45a1156cc47afccdf547086dc08d82f. Exact hashes are in
s6-native-late-source-pins.json; extraction source fragments and generated
sources are pinned in the two factoring metadata files.

Current enclosing caller authority remains owned adapter plus H5, as specified
in session A's handoff (default f8c0ec72..., devnet63ad3e9c...). The unchanged
component source evidence is compatible evidence, not a current SDK/compiled
release association. No new release/artifact pins are claimed.

Accepted targets: s6-native-late-codec-targets.json. Import/tool pins are in the
matching -import-pins.json and -tool-pins.json. These are under
evidence/s126-current-caller-20261021. All 14 focused targets exit0,
sum wall 235.271s, peak RSS
3294298112 bytes, zero swaps. Receipts record exact
target, source revision/hash, tool/import/object hashes, command, exit, wall,
RSS, swap and complete printed axioms. Only propext, Classical.choice and
Quot.sound appear. Jobs ran one at a time under the atomic local Lean lock,
-j1 -M4400 with warm imports. No unchanged full replay or heavy NUC job ran.
No binaries or compiled Lean objects are distributed.

Failures are retained but excluded, including error-recovery axiom reports.
Child-decode v1/v2 corrected existential witnesses and actual constructor names;
v3 is accepted. Factoring v1 corrected a tactic array/list mismatch; v2 is
accepted. Whole frame attempts v1..v7 exposed proof-shape and automation limits;
the structurally split header/tail replacement passes as v10, after v8/v9
located the remaining interface and dependent-rewrite issue. Encoder v1 had
too much frame context, v2 a recursive broad simplifier, and v3 exposed only
the impossible child-error branches; explicit local branch proofs pass as v4.
Child-encode v1 rewrote a graph to reflexivity; v2 is accepted.

## Remaining enclosing obligations and next consumer

The next theorem must add exact reconstructed-byte equality to the actual
transition encoder result, using these complete header frames and the already
checked native snapshot/afterstate inverses. Then compose the outer1880 forest
codec, including the existing extracted outer encoder's full-carrier and callee
binding; it is absent from the legacy decoder extraction and cannot simply be
assumed or manually renamed into that namespace.

Actual first/first_decoded/adapter stage1 reuse still requires that complete
FullForestAcceptedRoundtrip law and actual installed caller ports: public1880
and proof57607 slices, instruction split10/11, same semantic statement, S1
prepared/challenge provenance, backend ports, checkpoint and ownership/capacity,
ordered reads, errors, allocation/abort and release observer None. S1's native
whole preparation and actual SDK correspondence remain open. S2 remains with
its transferred owner; no S2/S3/S4/S5/S9 track was changed.

No source decision is required for these unchanged native component functions.
Any candidate adoption still requires explicit equivalence and fresh authoritative
source/tool/artifact re-pins. Overall target not yet established.
