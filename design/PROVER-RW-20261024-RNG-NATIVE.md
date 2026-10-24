# Native dependency and actual body continuation

Branch `codex/cx-prover-rw-20261023`; parent `abbee7673d`, accepted proof
revision `f3e9539784`. Prototype/source inspection only. Target not yet
established. No shipped source, protocol, wire, feature, security-contract,
key, merge, push, ELF or timing change/claim.

## Dependency pin

The separate `tools/prover-rw-20261023/rng-native/prototype` pins
zeroize `=1.8.1`, getrandom `=0.3.4`, matching the native lock. The original
`rng-caller/` prototype and all exhausted ledgers are preserved. New Charon
and Aeneas closure outputs replace only the dependency-sensitive emissions
in the new namespace. All four emitted files are identical to the accepted
predecessor after namespace and comment removal, checked in
`rng-native/dependency-assessment.json`. This does not prove physical Drop.

## Error abstraction and exact remaining source transport

The weakest selected-callback value relation is: Ok secrets relates only to
Ok the same secrets, and **every** native entropy error relates to
Err verifier::Error::Entropy. The native source map_err discards both Os(e)
and RepeatedZeroBlock without reading e. The From call wraps e without
inspection. Partial writes and the provider's advanced cursor still belong
to the primitive draw event/state; discarding the final error interior must
not discard that event or reset state. No byte/error identification follows.

The accepted emitted map_err proof establishes this algebra for its explicit
uninstalled carrier. A representation-independent source noninterference
argument would need a justified transport of the primitive getrandom result,
source enum wrapping and error destruction through the pinned extraction
semantics. Existing templates provide no installed getrandom sort: transparent
Error exposes the unsupported core NonZeroI32 TPattern; opaque Error yields
an external type hole. Picking arbitrary NativeTypes, or using u8 as that
hole, is not transport. No new axiom, backend patch, carrier installation,
runtime conclusion, cap16 native instantiation or probability association is
claimed. The retained original niche failure is reused; it was not rerun.

Before: concrete model theorem quantified over `[NativeTypes]`, with native
carrier installation absent. After: the same boundary; no premise is removed
by packaging it into a relation or a Body record. E1 remains literally
`ProverCommitPublicNonce40.E1`; no freshness, independence, retry law or desired
execution equality is introduced. General cap8 draw inventory remains open.

## Actual producer

Direct Charon/Aeneas extraction now includes the actual secure entrypoint,
`prove_masked_with_attempt`, the borrowed reservation/build method, native
`MaskedFixtureAudit`, actual context/fingerprints/nonce accessor/Variant tag,
pre-reserved acknowledgment and durable boolean adapter. The new producer
has no u64 audit placeholder or owned-store/FnMut substitution. The existing
cap8 prototype remains uninstantiated: its old audit carrier is unchanged.

`ProverRwRngNativeProducer.selected_reservation_false` follows the selected S2
path from actual Public/public_bytes, compiled input, exact public hash input,
context encode and exact private-attempt binding hash input into the actual
reservation call. `selected_duplicate_fatal` specializes the native durable
adapter's false reply. `selected_io_failure` uses the adapter's error reply
and actual Error::kind call, returning fatal Semantic with the advanced store
and updated last_error. Assumptions are the named local public serializer,
two hash replies, context encoding reply and filesystem reply (plus error
classification on I/O error), not a Body/native execution equality. These
are conditional source-control facts, not a durable-store correctness proof.

`ProverRwRngNativeBuildControl` proves only MaskSampleExhausted maps to
Rejected, fresh acknowledgment succeeds once, subsequent acknowledgment fails,
and false reservation becomes fatal Semantic with the returned store.
`ProverRwRngNativeBuildPaths` proves wrong layout returns before reserve,
missing acknowledgment fails after reservation, and material-generation error
retains the advanced store and original error. Primitive deref/build replies
are explicit local assumptions in the latter two source-path lemmas.
`ProverRwRngNativeReservationInvariant.reservation_invariant` is a general
postcondition over arbitrary admitted suffix leaves: after successful reserve,
every returned outcome retains that advanced store; material success requires
admission of the exact explicit field-entropy clear call. It does not assume
successful clearing, nor establish physical memory erasure.

Before/after scope: the accepted prototype Body was FnMut(Secrets,L) ->
(L, Result<(Vec<u8>,u64),Error>) without a source instance. The new theorem
instead mentions the actual emitted prove_masked_attempt(public,compiled,S2,
hash,attempt,DurableStore) -> (Result<(Vec<u8>,MaskedFixtureAudit),Error>,
DurableStore), with the named local replies above. This is new concrete source
progress; it is not premise removal from, or closure of, the old cap8 theorem.
No hidden structure contains desired source-world/output equality.

## Local leaves and source assessment

All 16 opaque sorts and 35 external function interfaces remain explicit
`TypeLeaves`/`LocalLeaves`, uninstalled. Full signatures, source spans and
hashes are in body-adaptation.json/body-source-map.json and the audit. The
actual native audit/context/secrets/store structures are emitted concretely;
opaque nested native components are not silently installed by choosing types.

Primitive boundaries include filesystem reserve_fallible and io::Error::kind;
allocator/vector conversion and EncodingDomain creation; the explicit hash
function; scalar/option equality, clones and constants; Zeroizing access and
explicit erasure calls. Larger unproved source components remain separate:
material generation (including its own acknowledgment production), zero-factor
D derivation, mask application, public serialization, salt derivation,
audit arithmetic, semantic construction, commitments and prove_from_semantics.
None is relabelled as a proved primitive or durable implementation. The error
paths proved here exit before the latter arithmetic/proof components.

The host prefix file differs from the current worktree only in an unrelated
loop over coordinates7,6 versus two assignments at line607. The complete host
file and both hashes are retained; every referenced declaration span matches
current source literally, with shifted lines recorded. All28 other mapped
source file entries (including the selected prover/reservation files) match
whole-file hashes;29 total files are mapped. This reuse is not a new native identity
gate. The dependency pin receipt initially retained the old host revision
label; its immutable input hashes identify its exact prototype. Later source
proof attempts record parent revision plus immutable WIP snapshots.

## Retained failures and next producer

Aeneas body attempts1/2 stopped at fields read on opaque Compiled/DurableStore
structures; exposing the actual source structures resolved both. Attempt3
translated the producer;4 also included actual local equality/context/tag
leaves. Lean11505 exposed a trait-default macro kernel free-variable failure
and downstream compiler panics; the explicit equivalent nonrecursive default
expansion compiled at11506. No backend was patched. Failed elaboration,
notation, comparison-shape and dependent-rewrite attempts are retained, not
accepted; no resource failure or cap increase occurred.

The exact getrandom native sort/result/destruction transport remains the
primary blocker. Do not turn error erasure into native runtime correspondence
without that transport. Next body producer is the actual material generator's
acknowledgment/derivation control and its source sorts/leaves, then successful
native audit/status/event association with the cap8 caller. Physical cleanup,
successful bytes/context-to-Raw, L1/L2 and full ordered event correspondence
remain open. No shipped architecture change has been shown necessary or made.
Later adoption still needs all3 current ELF pins, native event/status gates,
H5 interleaved slowdown<=10% and quiet-host<15s; none ran here.
