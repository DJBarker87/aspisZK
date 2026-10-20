# R1 premises reacceptance draft (2026-10-20)

Status: DRAFT for lead acceptance at gap-map step 9 (C3). This document
restates P1–P7; it records no acceptance, new premise, deployed theorem or live
cluster attestation. X1 remains a separate settlement release gate.

## Artifact scope to be confirmed at step 9

All repository paths below are relative to the repository root unless prefixed
with `design/`, `lean/` or `evidence/` (relative to this research directory).
Source inspection is at `74f689738905518e54f8532eaf368e333cefbf16`.

- Adopted compact binary verifier: SHA-256
  `8cf8d84ed0fe340a190b4f40a9f953f0e0523370299ba3ec8bbed9d65b88ace3`,
  1,405,680 bytes, source `9a71031d3a95f838ac6d75bd5c58eeafeb62a9e1`;
  features `pool-adapter,private-leaf-salts` (dependency features
  `optimized-terminal,program-build`). Authority:
  `design/LEAD-REVIEW-FORMAT-ADOPT-20261020.md:31` and
  `evidence/format-adopt-20261019/artifacts-sha256.txt:8`.
- B1 Pool: SHA-256
  `121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548`,
  605,704 bytes; features `r1-split-checkpoint`,
  `pair-forest-source-invariant-audit`,
  `pair-forest-source-result-invariant-audit`;
  `evidence/format-adopt-20261019/artifacts-sha256.txt:12`.
- Runtime reference: **Agave 4.2.1**, specifically `solana-syscalls 4.2.1`
  `src/lib.rs:843–880,2540–2600` and `solana-address 2.6.1`
  `src/syscalls.rs:392–447`, as recorded in
  `design/J1-R16-R19-RUNTIME-RELEASE-20261015.txt` (reference-path paragraph).
  This is a local reference/replay pin; observed release-cluster version is
  still pending in that note. It is not a live-cluster attestation.
- SBF builder: `solana-cargo-build-sbf 3.1.13`, **platform-tools v1.52**,
  Rust `1.89.0-dev`, LLVM `20.1.7`; release, `--offline --locked -j 4`;
  native evidence uses Rust/Cargo `1.94.1`.
  `evidence/format-adopt-20261019/artifacts-sha256.txt:3–4`.
- Formal kernel/library environment: **Lean 4.32.0**, AspisFormal's pinned
  mathlib and the Aeneas 4.32 port; the final coherent source/object manifest
  and axiom audit must identify the exact closure (privacy LOG D63–D67).
  This draft does not substitute a version label for that manifest.
- Translator executable SHA-256 pins, from
  `evidence/stage2-refactor-extraction-20261020/pins/charon-input.json:3–5`:
  Charon `daad69bea1114042a2d2fbd3dfde99922b152d4f57023bf8edb83e5a6f336af8`;
  Charon driver `efdbe5b86c9f5f70c93810af08f358d4ecbaecf6f3e87517b1176689a8c28c45`;
  extended-static Aeneas
  `4632746db1bf6c3953f2971078965a2a5a8ad6cf5f75636b46b397bc50c550b5`.
  These are binary hashes, not an assertion of successful whole-cone extraction.

**Pin drift requiring lead resolution:** `design/STAGE2-REFACTOR-20261020.md`
records source change `7d4c136f0` and runtime-gated verifier
`0622ad3f19b81d71776f1a0b2fdb624cca3f371c7c4bccb14adc8ea1dfbc8090`
(1,403,912 bytes). It retains that source as a candidate after Aeneas failed.
Current `verifier.rs:396` exports `candidate::tx2_authenticated`; the current
function is at `candidate.rs:243`. Therefore the adopted ELF above must not
be described as a build of the current refactor. Step 9 must name whichever
verifier is finally accepted and re-pin its extraction/build evidence. This
housekeeping job performs no stage-2 extraction, refactor or acceptance.

## P1–P7 carried forward for R1

Ledger citations mean the exact output of
`git show origin/main:docs/assumptions-ledger.md`, numbered from 1, at
`origin/main = e7e2e29629b1d263c359c82e30c192a7d7b23f2c`.
They identify the V5-era premise, not R1 acceptance. The frozen source is
also saved by revision and SHA-256 in this job's receipt manifest.

### P1 — SHA-256 oracle properties

For the selected R1 verifier's Digest32 transcript/duplex and binary Merkle
calls, and Pool SHA-256 uses, assume the collision, target-preimage and
classical modeled random-oracle properties assigned to SHA-256 by the
respective event ledgers. Source backend: `programs/r1-cost-probe/src/lib.rs:11`
implements `Digest32::digest` by `hashv(parts)`; binary leaf reads occur in
`crates/aspis-r1-cost-probe/src/candidate.rs:124`. B1 marker seed/address use
`programs/aspis-pool/src/nullifier.rs:104` and its seed helper at `:75`. These calls
attach to the verifier/Pool pins above, not to the V5 ELF.

V5 source: **ledger line 36**. Functional SHA equality is P3, not ROM.
The universal global log embedding R10 and byte-grammar/source refinements
remain proof obligations; accepting P1 does not discharge them. X1's
truncated-marker blocking assumption is recorded separately below.

### P2 — Solana account and transaction semantics

Assume the selected runtime enforces ownership, signer/write permissions,
account locks, atomic CPI/transaction rollback and persistent writes. The R1
checkpoint provenance and immutable finalized proof/public buffers depend on
those rules plus the selected program's actual write paths. Attach this to
the verifier and Pool pins and the Agave 4.2.1 reference above.

V5 source: **ledger line 43** (locks, rollback, PDA, System CPI, writes).
R1 source anchors: `programs/r1-cost-probe/src/r1_pool_adapter.rs:210`
(checkpoint metadata), `:405` (finalization clears upload authority), `:946`
(stage 1 validates inputs and writes the checkpoint at `:985`), `:995`
(stage 2 invokes authenticated verification at `:1020`);
`programs/aspis-pool/src/pair_forest.rs:1710` (marker reservation before CPI).
The unkeyed checksum at `crates/aspis-r1-cost-probe/src/verifier.rs:284`
is not authentication. R15's covering/source argument and skipped-value
canonicality remain open; runtime ownership alone is not their proof.

### P3 — Syscall and System-program semantics

Assume `sol_sha256` hashes the concatenation of the supplied byte slices
according to FIPS 180-4. Assume `sol_create_program_address` hashes seeds,
program id and `ProgramDerivedAddress`, rejects on-curve results, and treats
the stored bump as an ordinary seed, without canonical-bump search. Retain
the J1.R16 failure-prefix and seed-limit contract. For B1, System
`*_with_seed` operations must validate the derived address and required base
signature; creation/allocation/assignment must enforce those checks.

V5 sources: **ledger line 35** (SHA callback), **line 43** (PDA/System CPI).
The specific J1.R16 contract is in
`design/J1-R16-R19-RUNTIME-RELEASE-20261015.txt` (two semantic statements and
reference-path paragraph). B1 source: `programs/aspis-pool/src/nullifier.rs:112`
(`Pubkey::create_with_seed`) and `programs/aspis-pool/src/processor.rs:1631`
(creation and recheck). Attach to Agave 4.2.1 and the Pool/verifier pins;
release-cluster observation remains owed. Syscall correctness does not prove
R10/R19 source-effect accounting or the ROM property.

### P4 — Readonly metadata projection

Assume the metadata observed by the extracted guard equals the runtime's
owner, signer, writable and executable metadata. This is exactly
`R16ReadonlyMetadataProjection observed runtime` at
`lean/R16ReadonlyMetadataBoundary.lean:23`: four component equalities,
not an SDK memory/borrow, custody, owner-authentication or reachability theorem.
The account guard consumes owner plus flags; the buffer guard consumes only
flags (`programs/r1-cost-probe/src/r1_pool_adapter.rs:183,202`).

V5 source: **no explicit projection entry**. **Ledger line 43** is the
related runtime umbrella, not this equality. This R1 premise is already P4
in the gap map; it must be explicitly considered at step 9. Its historical
runtime backing is the Decision 1h ELF, not universal evidence for either
R1 verifier pin (gap map P4). Attach to the selected verifier's guard
extraction and Agave runtime metadata; no new replay is claimed here.

### P5 — Stored bumps and hints authenticate existing accounts (F6)

Assume the required existing Pool/registry/token-owned images are created
only at their canonical PDA addresses by their authorized creation paths.
Then the stored-bump/hint checks authenticate the expected master, lanes,
registry side, checkpoint, pages and vault pair without a canonical search
on accepted settlement. B4 checkpoint/page and vault coverage is recorded in
`design/POOL-B1-FRESHNESS-PREMISE.md` section 5 and accepted by
`design/LEAD-REVIEW-POOL-B1-20261019.md` under “B4 and vault”.

V5 source: **no explicit stored-bump/hint premise**. **Ledger line 43** is
the related PDA/account umbrella; **lines 93–96** describe the different V5
bump-255 policy, not F6. Attach to the B1 Pool, verifier adapter and release
account formats in J1.R19. Current source anchors:
`programs/aspis-pool/src/pair_forest.rs:453,470` (master/lane checks),
`:2207` (checkpoint), `:98` (four Pool-only hints).

Boundary/counterexample to the stronger claim “matching stored bump proves
canonicality”: `programs/aspis-pool/src/pair_forest.rs:3937` constructs a
noncanonical key with a matching stored lane bump and the decoder accepts
it at `:3960`; the checkpoint/page analogue is at `:3971`. Thus P5 retains
the provenance premise; this draft does not assert that false stronger target.
No change to P5 or additional assumption is proposed.

### P6 — Translation and formal checking

Assume Charon, Aeneas, Lean and mathlib correctly process the exact recorded
sources, patches and generated terms. Attach to the three translator hashes
above, Lean 4.32.0 and the pinned mathlib/source manifest used for each
accepted proof packet, followed by the single coherent final replay and
standard-only axioms audit. A successful helper extraction says nothing
about an unextracted caller.

V5 source: **ledger line 41**. The V5 331-module replay is historical evidence,
not an R1 replay. The stage-2 packet using these tools failed before Lean
emission (`design/STAGE2-REFACTOR-20261020.md`, Open); P6 does not turn that
failure into source coverage. Missing re-pins, R14 and dependent bridges
remain open. No Lean run or theorem is added by this draft.

### P7 — Source-to-SBF build correctness

Assume Rust, LLVM, platform-tools and the SBF build preserve the semantics
of the reviewed source and locked dependencies in the exact ELF selected
for release. Attach to platform-tools v1.52 / Rust 1.89.0-dev / LLVM 20.1.7,
the recorded build features, locks, tool hashes and verifier/Pool artifact
hashes above; final source-to-ELF and reproducible-build evidence must be
for the selected pin.

V5 source: **ledger line 42**. Byte reproduction supports build identity,
not compiler correctness. The R22 checked-Aeneas versus wrapping-release
arithmetic bridge remains a source correspondence obligation (lead gap-map
note's overflow addenda); it must not be silently assumed under P7. The
adopted verifier and refactored candidate require distinct correspondence
receipts. This wallet-only lock refresh does not rebuild either SBF.

## Differences from the V5 ledger and acceptance checklist

The lead should record acceptance or rejection of **each P1–P7**, together
with the chosen verifier source/ELF, unchanged B1 Pool pin, exact tool and
formal manifest pins, and target runtime at step 9. Blank status here means
**pending**, not inherited acceptance.

| R1 reliance not explicitly listed in V5 | Existing R1 disposition |
|---|---|
| P4's four metadata projection equalities | Already named P4; ledger line 43 is only an umbrella. Needs explicit R1 acceptance/coverage. |
| P5's canonical-creation provenance for stored bumps and hints | Already named F6/P5; not the V5 bump-255 policy. Needs explicit R1 acceptance/coverage. |
| Checkpoint-only-tx1 provenance, finalized-buffer immutability, skipped-value canonicality | P2/R15 source/runtime boundary; not individually enumerated at line 43. Keep R15 open until its covering/refinement route is settled. |
| B1's truncated seed and master-base signing restriction | Existing **X1**, outside soundness target (T): Freshness-B1, MarkerSeedCR-224 and MarkerAddressCR in `design/POOL-B1-FRESHNESS-PREMISE.md` sections 2–4. Ledger lines 36/43 supply general hash/runtime umbrellas, not this exact 224-bit construction or the Pool's permitted signing uses. Keep the named blocking-only hash premises and freshness release gate separate from P1–P7. |
| Exact failure-prefix/syscall trace preservation and all-input query accounting | R10/R19 obligations, not consequences of ledger lines 35/43. No new trusted premise is introduced. |
| Release overflow behavior versus checked translation; current stage-2 source coverage | R22/R14 obligations, not covered merely by accepting ledger lines 41/42. |

The lead note's later addenda also retain M10 implementation hypotheses and
R9/R15 cross-stage linkage. These stay named obligations, not new premises
smuggled into P1–P7. This document makes no theft/privacy extension, numeric
security reallocation, live deployment claim, or stage-2 completion claim.
