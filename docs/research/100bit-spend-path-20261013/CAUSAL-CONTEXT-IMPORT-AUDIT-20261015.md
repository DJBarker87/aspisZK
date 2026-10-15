# Causal-context import provenance audit

This read-only audit covers the eight final Lean modules published in the bundles listed below. It compares recorded final-source and import pins with current worktree files and the source/object files actually present in the pinned NUC workspace, `/home/dombarker/project-offloads/aspis-r1-concrete-decoder-20261013`. Current worktree HEAD was `8e6c2b4cba1c54fe165f7436f5fc3ada1e1ae0f3`. No Lean build or replay was run.

The detailed hashes and per-import status are in [import-audit.json](evidence/causal-context-import-audit-20261015/import-audit.json). The audit inspected the final target sources and only import artifacts recorded in each frozen manifest. A source hash match establishes byte identity for that source file; it does not establish that the build can be reproduced from the captured imports alone.

| Bundle | Final target | Final source | Final object | Import artifacts recorded |
|---|---|---|---|---:|
| `lean-unified-opening-density-20261015` | `R1UnifiedOpeningDensity` | Match | Match | 4 direct; all source/object pins match |
| `lean-unified-query-density-20261015` | `R1UnifiedQueryDensity` | Match | Match | 4 direct; source pins match; imported object hashes were not recorded |
| `lean-unified-rho-density-20261015` | `R1UnifiedRhoDensity` | Match | Match | 4 direct; source pins match; imported object hashes were not recorded |
| `lean-unified-semantic-density-20261015` | `R1UnifiedSemanticDensity` | Match | Match | 4 direct; objects match; source hashes were not recorded |
| `lean-source-wide-exact-codec-20261015` | `R1SourceWideExactCodec` | Match | Match | 2 direct; all source/object pins match |
| `lean-typed-recovered-words-20261015` | `R1TypedRecoveredWords` | Match | Match | 2 direct plus 2 captured support imports; all recorded source/object pins match |
| `lean-typed-recovery-stability-20261015` | `R1TypedRecoveryStability` | Match | Match | 3 direct; all source/object pins match |
| `lean-spend-query-dichotomy-20261015` | `R1SpendQueryDichotomy` | Match | Match | 2 direct; source pins match; imported object hashes were not recorded |

The source imports in all eight final modules match their bundle source pins where those pins are present, and match the corresponding NUC `sources/` files where those files exist. The eight target source hashes also match the current worktree files and NUC source files. Each target's recorded object hash matches the NUC `objects/` file.

The following limits are explicit in the manifests and NUC workspace:

- The query and rho density bundles, and the spend/query dichotomy bundle, recorded import source hashes but no import object hashes. The corresponding NUC oleans are present, but there is no frozen bundle object hash to compare against.
- The semantic density bundle's `imports.json` records four import object hashes but no imported source hashes. All four recorded object hashes match NUC objects. Three source files are present in both the worktree and NUC workspace; `AspisV8R19.R572SequentialWordMass` has no source file in the NUC `sources/` tree. Its worktree source exists, but this bundle did not pin its source hash, so the recorded object cannot be tied to that source by this audit.
- The query bundle labels its Q22 source pin `Q22Law`; the module imported by the Lean source is `R0C.V3.Q22Law`. The recorded path/hash resolve to that dotted module, whose NUC source and object are present and whose source hash matches the pin.
- `R1TypedRecoveredWords` has two Lean `import` declarations. Its bundle also captured `R1MixedLeafEncoding` and `R1ExactLeafFieldCodec` source/object artifacts; these are recorded support dependencies, not direct import declarations in that file.

No missing NUC object was found among the recorded imports. The one absent NUC source artifact is `AspisV8R19.R572SequentialWordMass.lean`, described above; its pinned NUC object is present and hash-matched. The JSON preserves full hashes, module names, file paths, and the source/object pin-presence flags for independent review.
