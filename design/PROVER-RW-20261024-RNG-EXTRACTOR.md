# Isolated refined-error extractor continuation

Branch `codex/cx-prover-rw-20261023`, after reviewed a684b31c35. Candidate
only; no adoption, merge, push, installed-tool modification, shipped source
change, key operation, ELF identity claim or performance claim.

## Corrected release source

The selected source is `RealR1_client.rs:20–29`:
`prove_for_proof_accounts` calls `prove_masked_retrying_with` with the actual
closure `|k| generate_for_mask_nonce(proof_account(k)).map_err(|_| Error::Entropy)`.
`proof_account` remains arbitrary mutable `FnMut(usize) -> [u8;32]`;
the public nonce can depend on earlier execution. The generator is
`state_only_entropy.rs:211–242`, fresh zero64 per entered fill, cap16,
two private 32-byte seeds. D152 forbids switching to the 96-byte adapter.
Requirement3 of RNG-TRANSPORT is corrected, with its erroneous original
selection retained explicitly. E1 remains the literal conditional 64-byte law.

The actual Charon LLBC has structured declarations for entry0, outer
callback3, generator6, map_err7, actual inner disposal callback12 and From30.
Its `getrandom::fill`16 is opaque. `selected-source-assessment.json` retains
their complete statements/bodies, source bindings, target, options, nightly
rustc14210d and dependency lock pins. All five available project source
bindings match the host source. This is source extraction, not a primitive
installation or a native refinement theorem.

## What ran and what it establishes

All evidence is under
`docs/research/100bit-spend-path-20261013/evidence/prover-rw-20261023/rng-extractor/`;
drivers and small synthetic sources are in `tools/prover-rw-20261023/rng-extractor/`.

| Invocation | Exact scope | Exit | Wall seconds | Peak RSS KiB | Swap |
|---|---|---:|---:|---:|---:|
| build001 | pinned extended base | 0 | 48.160 | 588344 | 0 |
| build002 | initial refined candidate | 1 | 5.631 | 592948 | 0 |
| build003 | layering correction and scalar-operation guards | 0 | 34.038 | 592792 | 0 |
| build004 | preserve three outer records | 1 | 1.016 | 154716 | 0 |
| extraction001 | synthetic Charon, optimized Rust | 0 | 0.229 | 135696 | 0 |
| extraction002 | synthetic candidate003 Aeneas | 0 | 0.308 | 64416 | 0 |
| extraction003 | actual selected64 Charon, optimized Rust | 0 | 28.382 | 579228 | 0 |

`ledger.json` links exact command, receipt, source/dependency hashes, status,
timing, RSS and swap for every invocation. Each build used an independent
Docker systemd scope with verified MemoryHigh6G/MemoryMax8G/noSwap/Tasks64;
the compiler waited behind a file barrier until all four limits were checked.
The generic retained v7 compiler image was pinned by full digest and mounted
only job-owned copies. Extraction used the existing independently capped
launcher. Populated user build reservations plus each new8G were below55GiB.
There was no resource failure, cap increase, or unchanged failed rebuild.

The exact-pattern recognizer accepts only I32 with ordered
MIN..-1 | 1..MAX bounds, including each bound's type. A distinct pure node
emits `{x : I32 // x.val ≠ 0}`, without a scalar coercion or manufactured proof.
The synthetic output contains actual wrapping/From, both Result branches,
move, Copy, and terminal closure disposal. It has no external template file.
Refined unary/cast and binary/comparison paths explicitly reject; existing
Bottom, dummy-binding, borrow and disposal machinery was left unchanged.
No drop_as_no_op option was enabled. This is an executed translation probe,
not an operation-simulation proof, feature completeness proof, native
association, or Lean-checked output. No new theorem was added or compiled;
every new receipt's full axioms field is N/A. The prior mathematical subtype
lemmas and four standard-axiom reports are reused unchanged at their prior
mathematical scope only.

## Exact failure and mandatory stop

Build002 exposed a dependency cycle: TypesUtils already depends on
TypesAnalysis. The recognizer was moved into Types and concrete casts and
comparisons were guarded before build003. Both source states and failure
logs are retained.

Candidate003 inherits tuple-struct normalization: generated NonZeroI32Inner,
NonZero and getrandom Error declarations are aliases, although the refined
scalar remains distinct from I32. This does not validate the requested
preservation of outer records. Candidate004 attempts to retain exactly those
three records, but its name match mistakenly writes integer0 where Charon
requires opaque `Disambiguator.id`. Build004 fails at TypesAnalysis.ml:104.
The minimal next repair is to bind that ID and check it through its supported
ID API, then rebuild and rerun the affected extraction. No repair/build005
was attempted: the explicit 4-build ceiling is exhausted and requires review.
Do not describe binary003 as implementing source004.

The initial provenance collector also failed an overly strict equality check
between current and historical extension archives. It was a read-only
collection failure, not a build/extraction invocation. Comparison exposed
later Lean-side changes, now retained in extension-archive-difference.diff;
no difference was silently discarded.

## Provenance and remaining obligations

All retained OCaml source copies match cached original build inputs, whose
executable equals the installed extended binary (SHA4632746d...550b5).
The complete current extension patch is archived, not merely the historical
patch. Pinned base b59d5188 plus those extensions plus candidate-003.patch
reconstructs every source hash in build003; candidate-004.patch separately
reconstructs build004. Both assertions were checked during archival.
The copied55 Charon OCaml source files equal the installed Charon source
snapshot; cb50 remains its inherited accepted commit designation. The
snapshots have no .git directory, so this is not a new git provenance gate.
Lean4.32.0 and getrandom0.3.4/zeroize1.8.1 remain selected; no dependency
upgrade was used. Compiler image digest, opam package versions, patch/source
manifests, build recipes and receipts are retained. Fresh builds are recorded;
neither historical byte reproducibility nor an independent deterministic
candidate rebuild is claimed. Binary003 hash is
09af4fe5a40f2340b3b326e01b15b23d8e8a0a39e3ae25938f9033dd56d5fdc5,
size49424520; no binary is committed. The source004 failure leaves that
earlier binary in place. Its version label remains historical, so use its
hash and candidate003 source manifest, never the version string alone.

Before and after this continuation, existing native theorem statements and
premises are unchanged. No NativeTypes hole was filled, no assumption was
discharged or added, and no output-equivalence hypothesis was hidden in a
new relation. The existing extraction trust boundary does not by itself
certify this experimental feature. Its selected-operation simulation and
feature validation are still required before source association.

Actual selected64 Aeneas translation has NOT run. The actual OS primitive's
complete LLBC signature has no explicit provider/read-history argument.
The inherited backend has not acquired state/effect transport in this patch.
Therefore retaining partial/full buffers, advanced provider state and every
ordered read/error event across actual native fill is an additional open
binding obligation; it cannot be replaced by the stateless synthetic success,
an opaque primitive contract, a reset, or an error-as-extraction-failure rule.
The actual inner closure was inspected, not substituted with call_once16.

MIN/-1/1/MAX and zero tests; custom/OS errors; both entropy variants; Ok;
first/later partial-write Err; zero then nonzero; cap16; uninitialized/moved
locals; other patterns; and ADTs with Drop/borrow have NOT been executed as
the requested validation matrix. The synthetic source covers move/Copy,
wrapping, repeated-zero construction and source Result control only.
Negative behavior of the new guards is source inspection, not tested evidence.
No generic wrapper or synthetic test closes those actual-source obligations.

Budget: Lean213/220 (7 left), Kani44/60 (16 left), unchanged; extraction3/12
(9 left); backend builds4/4 (0 left). All old ledgers and failures retained.
Next concrete deliverable after review: repair the opaque-ID match, validate
the preserved-record output and operation relation, then extract/bind the
actual64 callback with the complete provider/event/error interface. No full
manifest was run. Both deployed targets remain not yet established.
