Public amount guard agreement, focused Lean 4.32 checks

The identical frozen PublicRawAmountGuard source previously checked under4.31
is checked here under4.32. PublicRawAmountGuardAgreement.payment_guard_iff and
nonzero_iff identify both predicates under the existing fixed fromCore map.
decoded_of_guarded_core_success proves:
 Core.serialize p = some bytes -> PureGuard.PaymentAmountGuard p ->
 exists wire, Raw.toWire (fromCore p) = some wire /\
 PublicByteCodec.decode bytes = some (SemanticPublicWire.toPublic wire).
The guard supplies the nonzero withdrawal shape; no source validator success
or caller reachability is inferred inside this module.

Both first attempts pass: guard6.353s/1264976KiB sampled group RSS, agreement
22.616s/3478816KiB. Process maximum RSS670072832/2943516672 bytes; process swaps0.
System swap was preexisting and is separately recorded, not assumed zero.
The pure guard theorem is axiom-free; the two iff lemmas use propext and the
final decoder theorem uses propext, Classical.choice, Quot.sound only.

Receipts retain exact commands, source/runtime hashes, checkout revision and
source snapshots. The runner uses lake env lean, -M3500, a sampled4GiB process-
group stop and180s timeout; this is not a cgroup. Imported Core/Agreement and
R1 objects were reused read-only, with original source/cache provenance in the
referenced prior bundle. No cold dependencies or unchanged regression reran.

The4.31 carrier bridge separately proves actual helper AND serializer success
imply this pure guard and serialization fact. Matching shared source bytes do
not produce a cross-version kernel theorem. Actual verifier reachability,
ASF8/account/metadata binding, extraction and runtime correspondence, and one-
kernel source closure remain OPEN. The frozen serializer core is unchanged.
