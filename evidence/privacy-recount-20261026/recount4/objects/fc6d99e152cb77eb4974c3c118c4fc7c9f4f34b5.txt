# Library callback bundle handoff

Branch: `codex/pv-cblib-20261027`; base: `bd47052f039ae2d96060acb5607fe652ebe193d4` (unmerged prover candidate). **Target not yet established.**

## Result and premise accounting

Candidate source-law supply: **0 → 4**, V177/op25, V180/op29, V185/op34, V186/op35. Stable publication is `R1Z.PV_CBL_CallbackBundle`, using its documented `Types`, `selectedAll` and `opN_source`/`opN_source_all` names. All laws are unconditional in their data inputs and retain the full Aeneas Result. See OPS.md for the complete 19-op table, crate/version/file SHA and receipts.

Before: these callbacks were arbitrary fields of the input dictionary. After: the published selected dictionary has the four supplied reference definitions, with source provenance and explicit bounded P6 native checks. **Canonical endpoint/deployment premises removed: 0.** No endpoint assumption was added or weakened; source selection alone does not instantiate shipped execution or prove RunJoin. Native/toolchain/deployed-code association, E1/E2, L1/L2/L3, client route and repository-wide dependency closure remain retained. The simulator and observer were not changed.

Supporting proofs cover generic copy termination/content, complete-Result array specification, pop reconstruction and field-copy identity, split arithmetic, SHA count/bit-length arithmetic, reference field shapes and wrapper/buffer/byte-join value specifications. These are not extra discharged library rows. One optional join-case draft is rejected and archived under drafts/ (39728).

## Final reserved audits

| ID | target | exit | wall | peak RSS KiB | swap | revision | axioms |
|---|---|---:|---|---:|---:|---|---|
| 39729 | R1Z/PV_CBL_CallbackAudit | 0 | 0:01.27 | 2625316 | 0 | 03992c1dc2c8409a6a4d4b4ad72613510c9ff955 | standard only: propext, Classical.choice, Quot.sound (subsets) |
| 39730 | R1Z/PV_CBL_SelectionAudit | 0 | 0:03.67 | 2625828 | 0 | 03992c1dc2c8409a6a4d4b4ad72613510c9ff955 | standard only: propext, Classical.choice, Quot.sound (subsets) |
| 39731 | R1Z/PV_CBL_FinalManifest | 0 | 0:01.05 | 2623072 | 0 | a917e33cd5417091292313c126782707deffcf06 | standard only: propext, Classical.choice, Quot.sound (subsets) |

The final manifest ran once: 73 accepted dependency modules, 185 printed declarations. With the manifest itself, 74 current-source active modules are accepted. This is the frozen own-module import/axioms manifest, not a repository-wide or deployed privacy replay. Exact targets, source snapshots, direct import hashes and metrics are in the numbered JSON/log receipts and manifest-source-pins.json.

## Budget and native results

Lean: **100/100**, 77 exit-zero compiles; all failed/recovery-sorry artifacts are rejected. Kani: **10/10**, three bounded passes, three non-verdict setup/selector failures and four timeouts. No checked ROW counterexample was obtained. Env-J IDs consumed: 39600–39731; next unused: 39732. Refusals are zero charged and IDs were not reused.

KANI-SUMMARY.md records each native run. Exact command/revision/hash/cap/metric records are in collected-receipt.json. Timeout GNU-time wrapper RSS excludes killed descendants and is not asserted as aggregate solver peak RSS. Timeout cgroups were checked gone. No stubs or force-soft substitutions were used. Array, SHA2-vendor and block-buffer-vendor Kani harnesses remain prepared only.

## Open source/native frontiers

- Digest/block-buffer: DIGEST-FRONTIERS.json records the exact loan/destructor preflight failures. Op208 has a verified extracted body/outcome decomposition, while its compress256 binding remains open. The op215 monomorphized artifact has has_errors=true and is rejected.
- Pure Path/String ops 26/28/30/31 remain OPEN; they are not filesystem-effect deferrals. The joint bounded join/String native run timed out. Optimized owned byte-join extraction still requires destructor semantics.
- Op33 remains OPEN after two timed-out owned-reference native checks; its mathematical value specification is not an extracted-source certificate. Op36 retains loan/destructor and missing native gate frontiers.
- Op32 is DEFER(pv-runjoin): recoverable allocation/capacity outcomes require native allocator/world association; Err was not replaced by Ok.

Std source extraction uses its recorded nightly-2026-06-01 rustc 1.98.0 source corpus; Kani uses bundled rustc 1.93.0. Their distinct source/native/deployed associations remain explicit. Cargo library versions and additional .crate archive checksums/file bytes are pinned in source-provenance.json and additional-library-sources.json.

## Cache and implementation custody

Requested cb3 lean-objects cache was absent after host deletion; no binary was copied from it. 74 accepted current-source own objects were retained from shared Env-J into the owned host lean-objects directory, with exact provenance in retained-own-cache.json. This does not certify the inherited dependency source closure. Imported ProverRw sources were read-only. Production Rust prefix is byte-identical to the base; Rust additions are confined to the cfg(kani) harness module. No production ELF change/rebuild is claimed. No shared infrastructure was modified.

## Next deliverable

pv-wire/recount 4 can consume the four stable bundle laws with the recorded P6 bounds and association caveats. Further source discharge requires validated loan/destructor extraction for the exact owned references, a closed compress256 definition and native gates split enough to obtain verdicts under the fixed caps. Retain allocator/world and all side-channel/client/deployment obligations until their separate joins are proved.

## Committed stages

```text
a917e33cd5 Freeze callback audit results and final library manifest
03992c1dc2 Freeze library support proofs and remaining extraction frontiers
9a0af338e3 Record digest finalization and update extraction frontiers
adef9df495 Preserve native timeout evidence and symbolic array preflight results
bd1ecb7ae4 Record array and digest extraction frontiers with symbolic copy drafts
6911addb1d Publish pure path-view laws and expose SHA compression frontier
1b71b2650f Publish vector callback laws and retain allocation-effect deferral
1220690620 Record library source pins and focused vector reference preflight
```

This report/receipt commit follows the listed source and audit freezes. Nothing was pushed or merged.
