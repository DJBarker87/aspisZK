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

Work in progress: directly extract `prover::prove_masked_attempt` and
`prove_masked_with_attempt`, native MaskedFixtureAudit, the borrowed reserve
call and PreReservedNonce. No owned-store/FnMut substitution is used here.
