# Formatter provenance audit

Branch `codex/pv-fmtaudit-20261029`, candidate base `505f8745ee0a99d3c0ae16cb5f8217ec35dfcc77`. Recount8/9 read from research snapshot `bbedfc018d67a8fa6208627e199ee336b628c17e`; their own immutable candidate/research pins are retained in `input-recount{8,9}-pins.json`. The candidate checkout's ledger stops before these recounts. No ledger, implementation, existing host source or cohort object was modified. Fresh outputs are confined to this job's private audit directory.

## Finding and provenance

The apparent axiom is **cached dependency metadata**, not an axiom declaration of the loaded carrier. In all four requested effective cohorts, `Aeneas.Std.core.fmt.Formatter` is a **def of Unit**, declared in **Aeneas.Std.Core.Fmt**. `Error` is also a definition of Unit. The root constant `core.fmt.Formatter` does not exist: that spelling is printer shortening. `DisplayUsize.fmt` is a **def declared in Aeneas.Std.Scalar.Display**, not Core.Fmt.

| Effective cohort | Core.Fmt object SHA-256 | Carrier kind | DisplayUsize.fmt stored axioms |
|---|---|---|---|
| b3q | `9de08e38c8b7e79e51532d13743864cdabb0edcae70585852fed2c56e8464c16` | def Unit | Formatter |
| event / runjoin32 | same `9de08e38…` | def Unit | Formatter |
| NDR | `63b8efa3940faa81bb26f1b6ea140b2d6b81c1f1155b3fafa0544f6e1e82b9fc` | def Unit | Formatter |
| authoritative manifest | same `9de08e38…` | def Unit | Formatter |

The manifest's full SHA is `d9187c800b7479f66ec6147e3c8e91c1158d382c4aa467bf678e76901b9a8c0e`. b3q and event match all 5,673 external entries. NDR has 24 different present objects plus one missing entry within this external universe; eighteen differences are Aeneas/AeneasMeta. D510's 118 differences concern its larger shared/project comparison universe, not just these external entries. `resolution.json` gives every effective path and hash, implementing the first-namespace-root rule. `fmt-physical-objects.json` lists **every physically present Fmt object in all recorded search roots**, including shadowed copies; all b3q copies have `9de08e38…`. No split companions exist for these Fmt objects.

Every cohort has the **identical Scalar.Display object**, SHA `3feaf753dd04e643be0f09c12fc001ad65dd8889de0ba462d19d61566fb3b9ce`. It was not in the eighteen-module repair rebuild. Direct traversal of the loaded carrier and numeric formatter's declaration types/values finds **zero axioms and zero missing constants**, in both b3q and NDR. The formatter traversal visits 17 constants; the carrier visits 3. In contrast, `#print axioms` reports Formatter for the numeric formatter and no axioms for the carrier.

`CollectAxioms.lean.txt` records the exact Lean 4.32 implementation: imports consult a persistent export-time axiom list instead of recursively walking the imported body. The original upstream Fmt **did** declare Formatter as an axiom. The later Unit repair replaced that declaration; retained consumers still carry its old list. Thus these observations do not establish a hidden actual Formatter axiom or kernel inconsistency. They establish a source-profile change and stale metadata. This does **not** make the formatter model faithful to Rust.

The source chain is:

1. Aeneas `b59d5188c082f704a418c7cb4e52ad69328002d1`, Fmt blob `e681e35a22d39b3233934613da2dcbf2254f03bb`, source SHA `26ac770dbf97ae2947a968818c307044262756bd67275101ac0c34fb817a81ce`: **axiom Formatter**, def Error = Unit. The lean432 patch leaves this file unchanged.
2. Archived source record `EJR_library-source-provenance.json`, revision `ccf554595212759d6d7f853f46a84c7c53444c30`, original-source archive SHA `7f2afc2861916ce1bcaa5520d2a649d8e1243b29f24e49ffcf733eb4d3812f84`, agrees with that Fmt source. Historical EJR Fmt object pin was `7c17a7af2952203781321279f0c569410d27bd9f1233fa3f5d1ec6f67a07f068`.
3. Formatter-repair source SHA `daeafff88224be0870aadb6c3bad73ae7c9375c2de9bbceb177ed2d183d6bdc5`, tracked under `stage2-generated-prefix-canonicality-formatter-repair-20261020/sources/Aeneas/Std/Core/Fmt.lean`, changes the axiom to def Unit and removes its TODO comment. It matches today's shared source exactly. The source diff is retained. Historical srcid3 profile-selection records themselves distinguish these two profiles.
4. The h4 coherent replay manifest pins the later `9de08e38…` object; b3q, event and the authority resolve that object. NDR has a separately built Unit-definition object. This audit verifies those endpoints; it does not invent a missing exact compiler-invocation trace linking each historical binary to source bytes.

## Source comparison scope

`source-inventory.json` records all 236 patched-pin module source hashes. All 27 available shared source copies were compared byte-for-byte: **only Core.Fmt differs**. Freshly compiling the original Fmt confirms its axiom declaration. The eighteen library modules identified by h4/D510 were then compiled individually from the exact patched pin into a fresh, namespace-complete plain-copy overlay, with one capped scope per module. The other 218 baseline objects are reused authoritative objects, **not a fresh full source build**.

Consequently **Core.Fmt is a confirmed source-content mismatch** in both observed object variants. Exact expression/module comparisons are recorded separately from source-origin claims. Generated helper names or proof-term changes across build instances are not evidence of changed source. This audit cannot name an exhaustive set of *all* source mismatches among 236 objects without fresh builds or authenticated input traces for the other 218. There is no sound inference from object hash equality/difference alone to the precise source a compiler read.

## Credited claims and hygiene

Recount8/9's candidate-closed union is 57 rows: 56 theorem rows and V270, the D219 Formatter-route inventory diagnostic. [CLOSING-AUDITS.md](CLOSING-AUDITS.md) gives each exact closing theorem, immutable evidence path, full normalized axiom set, and exit-zero receipt. **All 56 selected outputs are standard-only** (`propext`, `Classical.choice`, `Quot.sound`). No selected closing output contains Formatter or another nonstandard axiom. Historical failed/unaccepted outputs containing sorryAx affect V170, V183, V187, V214, V215, V226, V227, V234, V238, V240; their failed status is kept separate and does not contaminate the selected successful receipt. Universe suffixes such as `Classical.choice.{u}` are normalized, not misclassified.

All 56 theorem rows nevertheless import modules declaring these nine nonstandard axioms:

- `Aeneas.Command.Decompose.TestsRec.recAxOp`
- `Aeneas.Std.core.panic.panic_info.PanicInfo`
- `Aeneas.Std.core.pin.Pin`, `Aeneas.Std.core.pin.helper.PinHelper`
- `Aeneas.Std.core.sync.atomic.AtomicBool`, `Aeneas.Std.core.sync.atomic.AtomicU32`
- `Aeneas.Std.get_target`, `Aeneas.Std.get_target.spec`
- `Aeneas.StepArraySpec.Tests.const_array_spec._native.native_decide.ax_1_1`

`hygiene-final.json` gives explicit per-row import paths and source hashes. These are **hygiene findings, not demonstrated proof use**. V270 has no closing theorem; D219 audited 12,920 declarations in 321 selected project-family modules, not all imported library declarations. Its scoped result does not imply that the library has no axioms, nor does it certify native formatting adequacy.

## Formatting policy and remaining work

No direct formatter call occurs in the 56 closing source files. That textual fact and standard-only printed axioms are insufficient to certify transitive `(fmt-1)` compliance. A concrete proof cone must distinguish carrier types/dictionaries from executed formatting calls, and must cite a guarded-unreachability proof (a), an infallible-writer proof (b), or faithful writer/error-state semantics (c). A proven success Result alone is not automatically that call-cone certificate; observable stderr/JSON/Debug paths require (c) or approved removal.

The b3q numeric-formatter counterexample is **quarantined, not a credited closure**. The arbitrary rejecting-writer instance violates `(fmt-1)` and remains rejected. The literal-port refutation is standard-only and does not use the pinned formatter. V269/native Debug adequacy and the actual std/dependency closure remain open.

The object inspection recovered 46 complete project/Aeneas dependency cones with proof bodies included. None contains a formatter function; 42 contain only the Error carrier. These are surviving object-variant footprints, not a new native or release proof. Five additionally match the object SHA in the selected receipt. Ten rows remain unclassified because the exact closing object or import cone is unavailable: V184, V217, V218, V240, V247, V258, V259, V261, V264, V265. See [FMT1-CLASSIFICATION.md](FMT1-CLASSIFICATION.md), formatter-footprints{,-more}.json and receipt-recovered-objects.json. No (a), (b), or (c) certificate is invented for those gaps. The primary V270 outputs and nine printed roots are retained in V270-primary/. No row lacking an exact, checked call cone is silently classified as (a), (b), or (c).

Recommendation: retain the existing row-specific standard-axiom credit at its recorded scope; do not promote it to native/observer adequacy. Record the Unit repair as a distinct source profile, regenerate all affected axiom metadata in a fresh coherent candidate, and re-audit actual closing declarations. Remove unused library test imports. Obtain the missing exact proof/source cones and discharge `(fmt-1)` guards or implement a faithful model before any native formatting or D159 closure credit. Do not merely suppress the cached axiom warning or treat Unit as a source law. No ledger change is made here. Endpoint premises removed/added/weakened: **0/0/0**; T unchanged. Privacy target not established.

## Audit limitations and corrections

This is a partial exhaustive-source audit: 218 baseline objects were reused; a 236-file fresh library replay exceeds the assigned 60-run budget under the one-module-per-scope rule. Exact source provenance remains unresolved where input traces are absent. The source-profile counterexample and cached-metadata explanation are checked independently of that limitation. Ten closing proof cones also remain unresolved.

ROOT-CORRECTION.md records an initial missing package-root argument, the replacement run sequence, and initial preflight hashing outside its scope. Initial comparisons are diagnostic only for private helper/body differences. These are audit setup/procedural errors, not evidence against the candidate. Corrected comparisons use an explicit package root and capped preflight. No new theorem, native link, or privacy closure is credited by this audit.
