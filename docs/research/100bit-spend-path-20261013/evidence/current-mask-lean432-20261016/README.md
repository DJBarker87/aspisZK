# Current selected-mask arithmetic on Lean 4.32

The 24 selected targets pass on the pinned Lean 4.32 kernel: two generated
modules, six retained pure field modules, fourteen maintained extracted
arithmetic/prepared-multiplier modules, and two scalar-multiplication modules.
There are 75 `#print axioms` reports: 74 use only `propext`, `Classical.choice`,
and/or `Quot.sound`; one is axiom-free. No successful report uses `sorryAx`.
All targets exit 0. Maximum `/usr/bin/time` RSS is 2,987,088 KiB; all process
swap counts are 0. The summed controller wall time is 29.435 seconds.
These are focused checks, not a full frozen-manifest replay.

The source base is `b40d1cfffadbdf967f84cca23ea4e7f1553d564f`. Exact source
hashes govern the two new scalar files. Generated source provenance remains
`70f8edc9d7fc9fe0e8a0bb854698419ba3a8a2f0`, with the LLBC and production-file
pins retained in the staging manifest. No production Rust changed.

## Reuse and kernel boundary

Lean is 4.32.0, commit `8c9756b28d64dab099da31a4c09229a9e6a2ef35`.
The NUC's matching Aeneas library cache passed a capped
`lake --no-build --rehash build Aeneas.Std Aeneas.Tactic.RustAttributes` check.
Its 1,621 targets were already up to date; they were not recompiled. The raw
log retains unrelated cached library warnings. The 75 target axiom closures
are the relevant dependency checks and exclude `sorryAx`.

Six backend compatibility-patch source hashes and the library object pins
match the retained `aeneas-verif/lean432` harness. The checkout is dirty, so
its Git HEAD alone is not treated as a sufficient pin. The 32 translator
patch files were not audited by this port. Existing extraction provenance is
retained; this is not a compiler/extractor correctness theorem.

All six historical pure field sources and the fourteen maintained proofs are
reused byte-for-byte. Generated bodies are unchanged: Types replaces the broad
`Aeneas` import with `Aeneas.Std`; Funs additionally imports
`Aeneas.Tactic.RustAttributes`. Reversing those exact import edits reconstructs
the raw extraction bytes. No 4.31 `.olean` was copied into the new workspace.
This Lean 4.32 direct `lean -o` invocation emitted standalone `.olean` files;
the archive retains all emitted target objects. Downstream imports passed.

## Resources and retained failures

Every target runs alone under systemd with MemoryHigh=4G, MemoryMax=6G,
MemorySwapMax=0 and TasksMax=128, plus Lean `-j1 -M5000 -DElab.async=false` and
a 300-second timeout. There is no outer flock or dependency build. Receipts
record the live reservation calculation, including other populated Docker
scopes, against a 50 GiB host limit. Zero **process** swaps is not a claim that
the host has no pre-existing swap usage.

The initial ExactTowerBase preflight lacked a cached Mathlib import. Appending
the complete cache still failed because Lean selected the earlier Mathlib root.
Putting the complete same-revision Mathlib cache first fixed the import path;
no source change or cap increase was needed. Both failed attempt directories
and environment versions are retained. A misspelled module name was rejected
before a Lean invocation/attempt directory. The original staging kit had the
wrong top-level provenance and wrong six pure files; root rejected it before
transfer, and corrected source hashes were independently checked. The rejected
metadata is retained separately.

## Contents and scope

`proofs.tar.gz` contains 307 hashed files plus the port summary: source snapshots,
24 target objects, per-attempt raw logs/resources/receipts, import pins,
controller/executor, source-only kit, environment history and Mathlib path repair.
`manifest.json` gives exact per-target revision, source, object, import, command,
exit, wall time, RSS, swap and axiom records. `independent-audit.json` separately
checks the curated 24-target set against the worktree. The staging kit contains
clearly labelled unverified loop drafts; those drafts are excluded from this
checkpoint's 24 targets and 75 reports. Subsequent edits/checks of those drafts
are separate evidence.

The new scalar theorem proves actual extracted QM31-by-M31 multiplication
returns a canonical value equal to multiplication by the exact scalar embedding.
The complete mask/caller relation, verifier acceptance-to-terminal implication,
remaining transcript/sampler/commitment obligations, efficient extraction,
privacy and runtime/settlement release gates remain open. This checkpoint is
not an end-to-end 100-bit theorem or a new cost measurement.

| Target | Controller wall s | Peak time RSS KiB | Axiom reports |
|---|---:|---:|---:|
| AspisR1SelectedMaskProbe.Types | 1.139 | 2597288 | 0 |
| AspisR1SelectedMaskProbe.Funs | 1.781 | 2621272 | 0 |
| ExtractedMaskM31AddSub | 1.322 | 2603736 | 2 |
| ExtractedMaskReducerOps | 1.213 | 2590008 | 8 |
| ExtractedMaskReducer | 1.306 | 2600724 | 9 |
| ExtractedMaskTowerAdd | 1.196 | 2596316 | 3 |
| ExtractedMaskCM31Mul | 1.385 | 2608896 | 6 |
| ExtractedMaskQM31Mul | 1.249 | 2599868 | 1 |
| ExtractedMaskQM31Tower | 1.21 | 2670452 | 2 |
| ExtractedMaskQM31Exact | 1.365 | 2980800 | 3 |
| ExtractedMaskQM31Equality | 1.324 | 2981356 | 1 |
| ExtractedMaskArrayThree | 1.167 | 2589260 | 3 |
| ExtractedMaskPreparedState | 1.175 | 2595984 | 2 |
| ExtractedMaskPreparedClosure | 1.151 | 2590420 | 1 |
| ExtractedMaskPreparedComponent | 1.185 | 2598412 | 1 |
| ExtractedMaskPreparedMul | 1.366 | 2984704 | 4 |
| ExtractedMaskScalarMul | 1.149 | 2593496 | 2 |
| ExtractedMaskScalarExact | 1.49 | 2987088 | 2 |
| AspisV8R17.RawReducerNat | 0.56 | 532840 | 4 |
| AspisV8R17.QM31WordFormulas | 0.362 | 520340 | 0 |
| AspisV8R17.QM31WordResidues | 0.87 | 1009216 | 10 |
| AspisV8R17.QuadraticTowerOperations | 1.17 | 1208308 | 4 |
| AspisV8R17.QM31WordTower | 0.855 | 1207704 | 6 |
| AspisV8R15.ExactTowerBase | 2.445 | 2615852 | 1 |
