# Public preparation and caller prefix follow-up

The new all-outcome `SerializerWhole.frontier_eq` and `serializer_eq` transport
the actual preparation serializer into the existing checked serializer carrier.
They preserve errors, outer failure/divergence and the exact returned bytes.
`PreparationBinding.helper_supplies_serializer_success` then supplies the `hs`
premise of `PublicBinding.decoder_serializer_parsePublic` from actual
`r1_semantic.public_transcript` success. Both ASF8 variants are covered. The
same bytes, hash argument, C1 root and returned transcript are retained.

`actual_selector_eq` and `projection_eq` use a fixed copy of every source
carrier field. The supplied Public is the selector of the same returned
statement; no independent transition or desired public equality is assumed.

The original r18 translator fails on `Observer = Option<fn(Phase)>`, even with
opaque downstream boundaries. The exact production `first` body is retained
in the diagnostic LLBC, along with the failed receipt. Its body was not
shortened. Replaying that identical LLBC with the existing accepted static
translator succeeds. The binary is pinned by the tracked challenge-qm31
build recipe to SHA-256 `4632746d…550b5`; all 38 patched source files and the
backend lock match their tracked manifests. No extractor was built or changed.

The emitted first has four external globals. In `FirstCaller` the decoder is
instantiated with the checked actual decoder plus the fixed returned-carrier
transport; the semantic selector is the checked actual selector. `tx1`, the
observer function and the effectful error mapper are explicit universal
parameters. The entire emitted body is checked after those named bindings,
including `Some(mark)`, the same ASF8/proof/k inputs and all error branches.
`first_success` derives actual decoder success and equality of the public
passed to that continuation with the fixed projection of the decoded
statement. Its axiom closure contains no external global.

This is a caller-prefix result with an abstract downstream continuation. It
does not prove the downstream `tx1` body reaches `public_transcript`, nor an
SDK/runtime preservation theorem, nor account reachability or custody. The
SDK error carrier is generalized to a type with a distinguished
InvalidAccountData value; downstream errors are generalized independently.
The success proof does not inspect those carriers. Custody remains separate
from B's metadata projection premise.

Only focused targets were checked in capped Linux scopes (6 GiB high, 8 GiB
max, no scope swap); exact receipts, failed attempts, source and object hashes,
wall time, RSS, swap and each requested axiom report are in
`evidence/public-binding-followup-20261016`. No SBF or runtime harness was run.
