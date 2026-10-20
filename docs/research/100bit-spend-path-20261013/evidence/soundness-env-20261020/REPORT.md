# Soundness environment S — 2026-10-20

Source revision: `eb9b122b6856fd91c7681cd03bb8a8ce767ba3fb`.
Branch: `codex/cx-soundness-env-20261020`.

This is a source/import-closure build, not a proof that named hypotheses hold
for the deployed verifier. Verifier and Pool sources are unchanged.

## Scope and preflight

`manifest-S.json` extends the earlier five soundness roots with the requested
acceptance, extractor-cost, decoder-composition and Bin roots, plus current
Fold, R22, R13, Stage2, Wire, Sampler and Shared modules. Root aliases already
reachable under R1 names are not also requested under their short names.
The three generated Types owners use the tracked discriminant bridges; their
original generated variants are archival, not alternate environment objects.

The full `--require-complete` check fails: 1,278 source modules, 126 library
identities, zero source conflicts, 24 unresolved imports. See `preflight.json`,
`manifest-check.stdout.json`, and `source-resolution.json`. Independent resolved
components are processed in dependency order; `manifest-independent.json` passes
`--require-complete` for the maximal 1,106-module resolved subclosure; unresolved imports and failed
modules block all their dependent modules. No missing source is substituted
with an unrelated cached object or an unpromoted candidate.

## Environment and resource limits

Host paths alongside J are `aspis-joint-20261019/{sources-S,objects-S,evidence-S}`.
S has no fallback to J's objects directory. It uses J's pinned Lean 4.32,
AspisFormal package libraries and Aeneas backend. The library object identities
are recorded in `libraries.json`. J's sources and objects were never overwritten.

The private launcher follows run-joint's slot/global-lock and reservation pattern:
parallel slots 22:30–14:00 London, the global lock otherwise; populated cgroup
reservations plus the new cap must be at most 55 GiB. Each Lean run uses
`-j1 -M7000 -DElab.async=false`, MemoryHigh=6G, MemoryMax=7G,
MemorySwapMax=0 and TasksMax=64. The 7G maximum retains the common rules'
stricter Lean ceiling rather than increasing it to the generic 8G scope cap.
`RUSTFLAGS=-C link-arg=-Wl,--threads=4` is exported; no Rust gate is run.

304 J objects were reused only after recursively verifying current source SHA,
source receipt, dependency fingerprint (or older receipts' dependency timestamp
ordering), and successful log/object ordering. Their full prior receipts and
new immutable object hashes are retained. No module was retried.

## Staging incident

The initial reuse staging copied `.olean` files but omitted ten `.olean.*`
sidecars. Attempts 6485 (`AspisR1BatchedActualCounter`) and 6487
(`AspisR1BatchedReducerBridge`) therefore failed to open
`AspisV8R17/RawReducerNat.olean.server`. All ten sidecars were subsequently
copied from J, with SHA-256 and size recorded in `reused-sidecars.json`.
Attempt 6610 (`BatchedWeightsActualReducer`) then exposed the same bundle's missing `.ir` runtime data. `complete-reused-artifacts.py` copied all 15
retained auxiliary artifacts, including the five IR files; see
`reused-artifacts.json`. None of these three modules was retried; their
dependent modules remain blocked.

The first audit helper (6999) had a syntax error in its tuple loop pattern.
The replacement helper changes the source to iterate over entries explicitly;
6998 succeeds. The failed audit is preserved and is not source proof evidence.

## Source/import failure

Attempt 6802, `R1LiteralTranscript` (source `lean/LiteralTranscript.lean`),
fails on unknown `TranscriptView.Challenge`, `TranscriptView.Message`,
`UnifiedSampler.Prefix` and `UnifiedSampler.samp`. Its imports are
`R1LiteralTypedWords` and `R1SelectedTranscriptParams`; the latter's current
narrowed source imports the public sampler carrier, not the full sampler and
transcript definitions. This is a source/import-closure failure, not a memory
limit failure. No source repair or retry is performed. Dependents are skipped.

## Attempt budget and continuation

The resolved dependency graph would need at least 784 source attempts after J
reuse and the first three staging failures, exceeding the 550 assigned numbers.
Source compilation is limited to 6450–6969; 6970–6999 are reserved for
the mandatory declaration audit. No number outside 6450–6999 is used.

After phase 1, the driver continues with the requested hchecks, legacy soundness
and Bin roots first, preserving dependency order. Current and failed modules
are excluded from the continuation; a previously skipped module may be compiled
only if it had no earlier attempt. `status-phase1.jsonl` and `phase1-stop.json`
preserve the boundary. The launcher update for this boundary is installed by
atomic rename, preserving executing shells' original script inode.

One earlier direct launcher replacement happened during attempt 6678. Lean
successfully compiled `R1Line18Geometry`, printed its two standard-only axiom
reports, and GNU time recorded exit 0. The executing shell then read the
replaced script and corrupted its exit log. `wrapper-recovery-6678.json`
retains the original receipt, captured stdout/time hashes, matching source and
dependency fingerprint, and object hash. The source compile is recorded as
recovered success with wrapper exit 2; no compiler rerun occurs. Its earlier
skipped dependents can enter the continuation because they were never attempted.

## Results

Final measured results and root statuses are recorded in `summary.json` and
`roots-current.json`. `attempts.jsonl` records each source compile;
`axioms-batches.jsonl` records audit scopes. The audit calls the same
`Lean.collectAxioms` API as `#print axioms`, over every declaration owned by
current source modules, including definitions and opaque types. Standard-only
root results, Formatter-dependent declarations, and generated formatting-related
`_native.decide.ax_*` declarations must be distinguished. The latter are
pre-existing generated declarations, not new proof admissions. Raw audit logs
are retained, and the final parser handles wrapped axiom lists.

No binaries, keys or object files are committed. Remote objects, raw logs and
sources remain on the host for inspection. This report must not be read as
closing C2 while preflight, compiler, budget, root or audit blockers remain.

## Joint-import blocker and final audit limit

Attempt 6975 fails importing the 30-module audit batch because
`Stage2ContinuationTypes` and `AspisR1PublicPreparation.Types` both declare
`instDiscriminantVariantIsize`. Thus the successful per-module object/dependency
checks do **not** establish that the complete S union imports into one Lean
environment. C2 remains open. No namespace bridge or generated source is changed.

The last assigned attempt, 6970, changes the audit strategy to separate import
environments, preserving the joint-import failure. Its helper fails to elaborate
on `liftIO` and `CoreM.toIO'`; it obtains no further axiom reports. No attempt
outside 6450–6999 is used. Final audit coverage is **790/820 current modules**;
the blocked batch's 30 modules are listed in `axioms-audit.json`. There are three
failed audit helpers/probes (6999 syntax; 6975 joint declaration collision;
6970 API-name resolution), distinct from the four failed source attempts.

The successful module graph has 820 current modules (304 retained, 516 compiled,
including the recovered compiler success), four failed modules, and 454 skipped.
25 of 36 Bin roots are current. The four requested acceptance/extractor/hchecks
terminal roots are blocked. `roots-current.json` gives exact blocker chains.
`coherence-final.json` verifies hashes and dependency fingerprints for every
current object plus all 126 library identities; its scope is the per-module
graph, and the separate joint-import probe fails.

## Measured totals

Host receipt interval: **29m 23s** (1,762.972 s, first retained receipt to last
audit log); peak RSS **4,615,096 KiB / 4.40 GiB**; process swaps **0**.
All 550 assigned numbers were used: 520 source compiles and 30 audit attempts.
No source module was attempted twice; the final hash/fingerprint check confirms
all 820 current objects and 126 library identities still match their receipts.

The successful audit inspects **22,173 declarations in 790 current modules**.
786 audited modules have only standard axioms across their owned declarations.
The four modules with Formatter-dependent declarations are:

- `AspisR1PrefixAggregateParser.Funs`
- `AspisR1PublicPreparation.Funs`
- `AspisR72Sampler.Funs`
- `AspisV8R19.SamplerWordRead`

The audit additionally lists 144 declarations depending on generated
formatting-related native-decision axioms (within those modules). It makes no
whole-closure standard-only claim. 23 current Bin roots have complete standard-only
owned-declaration audits; `BinWirePublicLengths` and `BinWireEnvelopeLengths`
are current but belong to the 30-module unaudited batch.

Full raw audit outputs, failed source outputs and the wrapper-recovery records
are committed here. Other raw source logs remain at their exact host paths,
with SHA-256 and byte sizes in `log-manifest.json`; every source attempt's
exit, time, RSS, swaps, source hash, dependency fingerprint and complete emitted
`#print axioms` lines are in `attempts.jsonl`. No further Lean run is authorized
within this exhausted allocation.
