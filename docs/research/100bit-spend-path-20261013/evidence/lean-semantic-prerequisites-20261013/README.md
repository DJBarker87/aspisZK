# Lower semantic import prerequisites

Focused source replay for lower `R0`, `R0FS`, and `R0C` prerequisites of the
pinned semantic import path, at worktree HEAD
`3c17bdf902eac67d12796ef029007305b358821e`. The pinned runner was
`/home/dombarker/project-offloads/aspis-r1-concrete-decoder-20261013/compile-one.sh`,
using Lean 4.32.0, `MemoryHigh=4G`, `MemoryMax=6G`, `MemorySwapMax=0`,
`TasksMax=128`, and interpreter threshold 5000 MB. Sources were copied from
the worktree unchanged; no theorem or premise was edited.

| Target / attempt | Source SHA-256 | Result | Wall | Peak RSS | Swap | Note |
|---|---|---:|---:|---:|---:|---|
| `R0/OpeningAlgebra` a | `4f36236f066acac2a4164174e5a7176a521bca0084c906d7e019bdc3d450a4a1` | pass | 2.01 s | 3,522,112 KiB | 0 | Standard axioms. |
| `R0/BadSetBounds` a | `4e1110b8e1c5a02996ec19174ef399d8d9c49cb081cb405d76ad133ade433a22` | pass | 2.51 s | 3,531,588 KiB | 0 | Standard axioms. |
| `R0/Binding` a | `b150fe57b04aba6f5f8a506f344c6e6a5b0d3269ceb2dcb1c58fe1cd5ecdae42` | fail | 1.95 s | 3,512,668 KiB | 0 | `quotient_from_final`: unknown `AspisV5ComponentCQM31Representation.deployedPrimeFact`. |
| `R0/Round` b | `ac4c9c948dc832a1abb54ce73ac3889e169b8ca4a144e3722986141cb40f33e8` | pass | 1.59 s | 3,426,308 KiB | 0 | Refreshed against current `RoundNormalization`; standard axioms. |
| `R0/FibreRestoration` a | `f8c3800d14d941c92cc697fa4a0e36c4a722dc22e795d2283ba6651ba910ca2a` | pass | 1.86 s | 3,520,852 KiB | 0 | Refreshed against current `Round`; standard axioms. |
| `R0/Binding` b | `b150fe57b04aba6f5f8a506f344c6e6a5b0d3269ceb2dcb1c58fe1cd5ecdae42` | pass | 2.08 s | 3,531,900 KiB | 0 | Same source passes after `Round` and `FibreRestoration` refresh; standard axioms. |
| `R0FS/Protocol` a | `e3934ccf98f6578656e5c48cc6f3d5f6275808fa7778c197105227c09949a89c` | pass | 1.99 s | 3,543,516 KiB | 0 | Refreshed against current `Binding`. |
| `R0FS/Hypotheses` a | `937e18c5770da39b298dcfb7ff2d635e98069996ae18dc1c4158b28029ecb7b7` | fail | 3.61 s | 3,548,036 KiB | 0 | Lines 200, 281: unknown `deployedPrimeFact`. |
| `R0/Ledger` a | `0d71838ec05d7e9f983e934d602848b7e5254008467558c38826b1d33adc6d8e` | pass | 1.67 s | 3,513,120 KiB | 0 | Refreshed owner of `grouped_cardinalities`; standard axioms. |
| `R0FS/Hypotheses` b | `937e18c5770da39b298dcfb7ff2d635e98069996ae18dc1c4158b28029ecb7b7` | pass | 3.72 s | 3,574,428 KiB | 0 | Same source passes after `Ledger` refresh. |
| `R0FS/V2` a | `0a9ee117ea525400c1bd6ddf2725f084c929b6bba0e8164a0bbbf597a108f9c8` | env miss | 0.46 s | 1,075,148 KiB | 0 | `FS2.DuplexDecodes.olean` absent from first object namespace. |
| `R0FS/V2` b | `0a9ee117ea525400c1bd6ddf2725f084c929b6bba0e8164a0bbbf597a108f9c8` | pass | 2.48 s | 3,543,692 KiB | 0 | After linking missing objects in its imported FS2/AspisV8 closure; standard axioms. |
| `R0C/SemStatement` a | `065e73821e28582b1e08073fb64383f0bec7342cf8fed0cbbe3bd68430fab90d` | pass | 1.67 s | 3,543,136 KiB | 0 | Refreshed against current `R0FS.V2`. |
| `R0C/V3/R0Q` a | `e1bdb96a86c81b143c6962f904ccc2c4f291ec7f81dcdc0f54534cfa83ba0fb9` | env miss | 0.27 s | 620,020 KiB | 0 | `AspisV8R19.R599CanonicalFieldTuple.olean` absent from first object namespace. |
| `R0C/V3/R0Q` b | `e1bdb96a86c81b143c6962f904ccc2c4f291ec7f81dcdc0f54534cfa83ba0fb9` | fail | 17.96 s | 3,534,404 KiB | 0 | Resolved imports, then source hit unknown `AspisV5ComponentCQM31TowerExact.QM31Exact` at line 155; later diagnostics cascade. |
| `R0C/ModuloField` a | `b37fdc5f9fa6f83c068566448964a9f168578c23164d8a02a14ae931e3db09f0` | fail | 1.74 s | 2,462,888 KiB | 0 | First diagnostic: line 13 cannot resolve namespace `AspisCircleGroupOrder`; `open` fails and later `WideExact` errors cascade. |
| `R0C/ModuloField` b | `2c0f918c9eb6ac2ab93e07f955d3a5423a968dcefa01fcde58b31feb19d86594` | pass | 1.49 s | 2,475,732 KiB | 0 | Added direct import `AspisFormal.CircleGroupOrder`; standard axioms. |
| `R0C/OpeningSamplerBounds` a | `2272c45d33e7da7db78369543b6c6a66689744d729a4dc4beea8d8534657928a` | pass | 3.09 s | 3,530,868 KiB | 0 | Refreshed against passing `ModuloField`; standard axioms. |
| `R0C/ConcreteSlack` a | `a716935c3d2ab4cb782e1b2b1e591f43e95db60f68b231c691a89a922a318a19` | pass | 1.63 s | 3,543,776 KiB | 0 | Refreshed against passing `ModuloField`; standard axioms. |
| `R0C/SlackStatement` a | `2539373feaa6f95699d0d9eeed0d54867e6fad294971e86e0bdf78d335358031` | pass | 1.52 s | 3,532,188 KiB | 0 | Refreshed against current `R0FS.V2`; standard axioms. |
| `R0C/SlackDensity` a | `15dfa5eb7e101f8772df8c7e8949be8b1518e97d04ea37bba795f7e80e692bf5` | pass | 2.21 s | 3,551,628 KiB | 0 | Refreshed against current `SlackStatement`; standard axioms. |
| `R0C/SlackObstruction` a | `1b985a20ae222b944bec9f9fd0eae5c5caf4ac5b5def132921b6b078f970da7b` | fail | 1.62 s | 3,519,960 KiB | 0 | First diagnostic at line 38: unknown `deployedPrimeFact`; stale `SlackStatement` lineage. |
| `R0C/SlackObstruction` b | `1b985a20ae222b944bec9f9fd0eae5c5caf4ac5b5def132921b6b078f970da7b` | pass | 1.82 s | 3,543,736 KiB | 0 | Same source passes after refreshing `SlackStatement` and `SlackDensity`; standard axioms. |
| `R0C/SlackBits` a | `0d43a896fbcad219286e1ebd757256753f66e2cfe969e2ed2c1eca53da0ccfa6` | pass | 1.65 s | 3,546,988 KiB | 0 | Refreshed against current `SlackObstruction`; standard axioms. |
| `R0C/V3/DuplexQ` a | `17bcf865faf637926946a9a8d05c8b2ebd37148c29671f587b82f39e0e08e2bd` | pass | 6.44 s | 3,576,464 KiB | 0 | Refreshed concrete q22 decoder; standard axioms. |
| `R0C/V3/DuplexQDensity` a | `d5f5b08b86fdc99aed58a67bbda3caa21bf4abd9b281884b8b390092dec52494` | pass | 3.19 s | 3,553,724 KiB | 0 | Refreshed against current `DuplexQ`; standard axioms. |
| `R0C/V3/DQChain` a | `68bfc32c20d9333be9660652b6bf217b7090942dcf195c41a17b1c672505f8c0` | pass | 2.35 s | 3,547,424 KiB | 0 | Refreshed against current `DuplexQDensity`; standard axioms. |
| `R0C/V3/DQDecodes` a | `5dc040b0d21b5080fbf33c9191c07a98024771482eca459e55a27a17925de2a3` | pass | 9.38 s | 3,617,824 KiB | 0 | Refreshed against current `DQChain`; standard axioms. |
| `R0C/V3/R0Q` a (refresh) | `e1bdb96a86c81b143c6962f904ccc2c4f291ec7f81dcdc0f54534cfa83ba0fb9` | pass | 5.41 s | 3,560,368 KiB | 0 | Fresh object after q22 closure refresh. Runner attempt label `a` reused; archived locally under `remote/refresh/` so the earlier `a` environment-miss record remains intact. Standard axioms. |

The first `R0/Binding` replay showed a stale constant after refreshing only
`OpeningAlgebra` and `BadSetBounds`. Root identified the unrefreshed
`R0.FibreRestoration` path through `R0.Round`; rebuilding those two owners
made the unchanged `Binding` source pass. The first `R0FS.Hypotheses` replay
failed in its two uses of `grouped_cardinalities`; refreshing its owner
`R0.Ledger` made the unchanged source pass. `R0FS.V2` first stopped on a
missing namespace object; after linking only absent paths from existing pinned
object roots, V2 passed. `R0C.SemStatement` then passed against refreshed V2.

For the other direct R0C branch required by `R0P.SemD3Glue`, the final
`R0C_V3_R0Q_overlay-links.json` and
`r0c-r0q-import-sources.json` record its 62-module source closure. Only
missing overlay paths were linked, preferring the pinned line18 object root,
then generic `objects2`, then the R0 cache; existing overlay files and links
were left untouched. The initial `R0C/V3/R0Q` attempts first had an environment
miss and then exposed stale `QM31Exact` through cached `DuplexQ`. The focused
refresh rebuilt the unchanged concrete field/query chain. `ModuloField` first
failed because narrowing `WideTower` had removed a transitive namespace
import; adding the direct `AspisFormal.CircleGroupOrder` import made it pass.
The next failure, `SlackObstruction`, came from stale `SlackStatement`/
`SlackDensity` declarations; refreshing those owners made the unchanged
`SlackObstruction` source pass. The refreshed chain through `V3/R0Q` is green.

The guarded runner unlinks a stale output symlink before compilation. Failed
outputs (`R0/Binding` a, `R0FS/Hypotheses` a, the original `R0C/V3/R0Q` a/b,
`R0C/ModuloField` a, and `R0C/SlackObstruction` a) remain recorded with their
first diagnostics. Passing output objects are kept in `objects/`. The latest
`R0C/V3/R0Q` refresh reused runner attempt label `a`; its exact receipt and
logs are stored separately in `remote/refresh/` so the earlier environment
miss record in `remote/` is not overwritten. No `R0P` target was compiled by
this worker.

For route inventory only, `R0P.MaskSemantics` imports `R0P.MaskD2`, whose
lower path runs through `R0P.MaskProtocol` and `R0P.SemD3Glue` to
`R0C.SemStatement`, `R0FS.Hypotheses`, and `R0C.V3.R0Q`. `R0P.MaskValue`
directly imports `R0P.SemDeg` → `R0P.SemD3`; its transitive source path
through `SemDecision`/`SemView`/`SemSource` also imports `R0C.SemStatement`.
No claim is made about runtime resolution or compatibility of old cached
`R0P` objects.

Receipts, compiler output, timing data, and source hashes are in `remote/`
(`R0Q` refresh under `remote/refresh/`).
Source snapshots and source-closure inventories are in `sources/` and the
top-level JSON files. The 22 target `.olean` outputs are in the deterministic
`compiled-target-objects.tar.gz` archive (SHA-256
`a396a8f8b4b2bd5b2b09df40a1563399ce6a16fc985bc6fdf679319318d4c89c`); they
are also left loose under `objects/` for the current checkout. To restore them
in a fresh checkout, extract the archive at this directory so its `objects/`
paths are recreated. The archive contains only this bundle's target outputs,
not dependency-cache objects.
