# Owner decision requested — proposed only, not adopted

Existing runtime SHA trust supplies SHA value semantics at its admitted boundary.
Allocator and TrustedStd supply their named allocation/library semantics;
AeneasExtraction is a source/extracted association, not an implementation of
this external PDA declaration. None of those alone establishes the compound
PDA syscall or Ed25519 decompressor. Do not broaden any existing row implicitly.

Proposed narrow text, `FixturePdaRuntime`:

> For the seven explicitly enumerated JHs fixture PDA invocations, with the
> pinned solana-pubkey 2.4.0 ABI, valid readable seed descriptors/bytes and
> program-id bytes, valid disjoint writable output, and sufficient runtime
> compute admission, sol_create_program_address agrees with the guarded
> JHs_PDA.derive model: ordered seed concatenation, program-id bytes and ASCII
> ProgramDerivedAddress are hashed using the existing runtime SHA semantics;
> the exact digest is rejected iff the pinned curve25519-dalek 4.1.3 compressed
> Edwards-Y decompressor succeeds. The model OnCurve square-root predicate
> agrees with that decompressor, including its handling of noncanonical Y
> encodings and the sign bit. A successful syscall writes exactly the digest
> and returns zero; an on-curve digest returns InvalidSeeds (1). Seed-limit
> failures are handled by the SDK wrapper before the syscall. Traps, invalid
> memory, exhausted compute, unlisted calls and other runtime effects are
> excluded. This row supplies no concrete digest equation, no off-curve fact,
> no decoder result, no caller acceptance, and no artifact identity.

Scope: **fixture non-vacuity only**. Soundness quantifies over op38's values
under lead ruling (s); this proposal does not change that theorem or its trust
list. Owner adoption and the actual deployed runtime/artifact association are
still required. No runtime version is inferred from the program Cargo.lock;
the validator implementation is a separately pinned artifact obligation.

Recommendation: first prove all seven SHA equations using bounded per-round
certificates. Keep the seven off-curve facts named until they are proved or the
owner authorizes a narrowly pinned runtime observation route. This proposal
alone does not make those facts true and is not an authorization to assume them.
