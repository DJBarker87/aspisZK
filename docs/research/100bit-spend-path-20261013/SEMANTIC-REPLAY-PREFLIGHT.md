# Semantic replay import preflight

Read-only inventory for reusing `R0P.SemD3Glue`, `R0P.MaskProtocol`, and
`R0P.MaskD3Glue` from the pinned runner. No builds or source changes were made
for this inventory. The worktree base HEAD is
`0dbaf0c8d576a8da71e031b89cef2c9083c67cca`, but some listed sources are
modified in the worktree. The table pins the source snapshot inspected here;
historical attempt hashes below identify the exact earlier inputs, where
applicable.

## Runner namespace search order and object status

Pinned workspace:
`/home/dombarker/project-offloads/aspis-r1-concrete-decoder-20261013`.
`run2.py` prepends its `objects/` directory to the `LEAN_PATH` in
`environment-base.json`. The effective first four object roots are:

1. `/home/dombarker/project-offloads/aspis-r1-concrete-decoder-20261013/objects`
2. `/home/dombarker/project-offloads/aspis-line18-import-footprint-20261013/objects`
3. `/home/dombarker/project-offloads/aspis-fs-generic-20261006/objects2`
4. `/home/dombarker/project-offloads/aspis-r0-20261006/cache`

The disk-availability inventory, updated with the final root receipts, is below.
A later-root object is not proof that Lean will resolve it: the current runner
contains partial namespace directories, and Lean does not fall through those
directories per missing file. A namespace overlay must contain/link the
required objects before a focused import check.

| Module | Current workspace `objects/` | First base object root | Available object (disk inventory) | State relative to current sources |
|---|---|---|---|---|
| `R0.Dot` | owned overlay object | — | current overlay | Green attempt `R0/Dot-d`, source SHA below |
| `R0.OpeningWeights` | owned overlay object | — | current overlay | Green attempt `R0/OpeningWeights-c`, source SHA below |
| `R0.RoundNormalization` | owned overlay object | — | current overlay | Green attempt `R0/RoundNormalization-a`, source SHA below |
| `R0.OpeningDefinitions` | owned overlay object | — | current overlay | Green attempt c in the frozen reuse checkpoint |
| `R0.ChordImage` | owned overlay object | — | current overlay | Green attempt c with the symbolic child-zero proof |
| `R0.Chord` | owned overlay object | — | current overlay | Green attempt c after predecessor refresh |
| `R0P.MessageDescent` | owned overlay object | base copy exists | current overlay wins | Green `R0P/MessageDescent-a`; imports new `Wide.SubfieldDescentCore` |
| `R0P.SemD3Glue` | no owned current object | symlink resolves to generic cache object | `objects2/R0P/SemD3Glue.olean` | Old compiled object; its source imports the refreshed `MessageDescent` and refreshed parser/FS dependencies |
| `R0P.MaskProtocol` | no owned current object | symlink resolves to generic cache object | `objects2/R0P/MaskProtocol.olean` | Old object downstream of `SemD3Glue` |
| `R0P.MaskD3Glue` | no owned current object | symlink resolves to generic cache object | `objects2/R0P/MaskD3Glue.olean` | Old object downstream through the mask chain below |
| `R0C.SemStatement` | absent | absent | **present** at `objects2/R0C/SemStatement.olean` | Present on disk; effective resolution through partial namespace overlays still needs a focused check |
| `R0FS.Hypotheses`, `R0FS.Protocol`, `R0FS.V2` | no owned current object | symlinks resolve to generic cache | corresponding `objects2/R0FS/*.olean` | Cached objects on the R0 opening path; source owners unchanged, but upstream OpeningDefinitions/Binding lineage is old |

The previous note [`FIELD-IMPORT-INVENTORY.md`](evidence/lean-d18-opening-weights-20261013/FIELD-IMPORT-INVENTORY.md)
records the earlier `R0C.SemStatement.olean` miss. An object is available on
disk at search root 3, with source
`docs/research/v8-r0-close-20261007/lean/R0C/SemStatement.lean` (SHA-256
`065e73821e28582b1e08073fb64383f0bec7342cf8fed0cbbe3bd68430fab90d`). It
directly imports `R0FS.V2`. Its source hash still matches the previous semantic
inventory, so this establishes a candidate object location, not effective Lean resolution;
its import chain still inherits the older `R0FS`/`R0.Binding` objects until
those owners are refreshed.

The initial focused receipts captured here showed `R0.RoundNormalization`
compiled green at source SHA `af1a59d786104ba215c5c241c9ac7b32fff3c828b51456e6320522792584c0c4`.
`R0P.MessageDescent` compiled green at source SHA
`79c8eae0dee9f4a094646b36ac44271d098a62a155008ff3b85549b9ac13be2c`.
The first `R0.OpeningDefinitions` attempt at SHA
`fd3b3efc5dbcb7681dc54053a5caf7b8005f618fb7e2ad37c7c0764a6fa3da27`
exited 1 with kernel errors for missing
`AspisV5ComponentCQM31Representation.deployedPrimeFact`. Its cached
`R0/OpeningDefinitions.olean` at that inventory point came from the older
object lineage. `R0/ChordImage` first attempt SHA
`6e1e0f168f2de7f9923aa2f77cc8ce12fff15d6cfba49c4066e6655b95746536`
exited 1 (maximum recursion depth and then unknown `pairWord_zero`). This
attempt predates the current `pairWord_zero` proof edit (current source SHA
`227b30a3343668da8ee9b4d19d732feacd1423615aba2462c00dca170a1c6a0e`).
`R0/Chord` attempt SHA
`ade2d0d7ccbaa66cac517578e8c4ead02b674d81fb1e2f1638f3746c2b01d189`
exited 1; its logs include the same `deployedPrimeFact` kernel error and an
unknown `interpolationLinear` in attempt `a`. These are historical attempt
outcomes, not the status of the later source refresh reported below and not
results about the semantic theorems.

## Relevant import ownership graph

The current source imports give this dependency chain (arrows point to direct
imports):

```text
R0C.SemStatement → R0FS.V2 → R0FS.Hypotheses → R0FS.Protocol → R0.Binding
                                                               ├→ R0.OpeningAlgebra
                                                               ├→ R0.BadSetBounds
                                                               └→ R0.OpeningDefinitions
R0P.SemD3Glue → R0P.MessageDescent
               → R0C.SemStatement
               → R0FS.Hypotheses
               → R0C.V3.R0Q
R0P.MaskProtocol → R0P.SemD3Glue
R0P.MaskD2 → R0P.MaskProtocol, R0P.SemD3Glue, R0C.Counting
R0P.MaskDuplexDecoder → R0P.MaskProtocol, R0P.SemDuplexDecoder, R0C.V3.BSOk, FS2.DuplexDecodes
R0P.MaskView → R0P.MaskProtocol
R0P.MaskBadSets → R0P.MaskView, R0P.MaskD2
R0P.MaskSource → R0P.MaskBadSets, R0P.MaskDuplexDecoder
R0P.MaskSemantics → R0P.MaskD2
R0P.MaskPrefix → R0P.MaskSource, R0P.MaskSemantics
R0P.MaskNoHit → R0P.MaskPrefix
R0P.MaskEarly → R0P.MaskNoHit
R0P.MaskD3Glue → R0P.MaskEarly, R0P.MaskNoHit
```

`R0P.SemD3Glue.lean` also directly imports `SemD2`, `CircleSampler`,
`SemAccept`, `SemHonest`, `SemVirtualDeg`, and `SemPad`; their source paths and
objects were present in the generic object root. `R0P.MaskProtocol` and
`R0P.MaskD3Glue` have only old generic-cache object candidates in this inventory. On the
source graph, the smallest refresh chain for these consumers starts with the
R0 import owners (`R0.ChordImage`, `R0.Chord`, `R0.OpeningDefinitions`, then
`R0.OpeningAlgebra`/`R0.BadSetBounds` and `R0.Binding`), flows through
`R0FS.Protocol` → `R0FS.Hypotheses` → `R0FS.V2` → `R0C.SemStatement`, then
through `R0P.SemD3Glue` → `R0P.MaskProtocol` and the mask chain in the diagram.
`R0P.MessageDescent` is already an overlay green object; its current source
imports only `Wide.SubfieldDescentCore`, whose overlay object is present.
The target sources themselves are unchanged from the semantic source inventory
except for `R0P.MessageDescent`.

This is a source/import refresh map only. It does not select theorem premises,
state a semantic design, or claim a successful replay.

## Replay delta and unresolved refresh set

After this namespace inventory, root reported a green changed-source closure
for `R0/PolynomialPair`, `R0/ChordImage`, `R0/Chord`, `Wide/MatchedInstances`,
`R0/ListsResponses`, and `R0/OpeningDefinitions`. The final 24-target manifest
in `evidence/lean-reuse-checkpoint-20261013/` pins their object/source hashes
and green receipts, independently validated by root. It also includes the
green `Wide/SubfieldDescent` wrapper. These supersede the initial failures.

The exact target objects still unresolved in the inspected runner inventory
are `R0P.SemD3Glue`, `R0P.MaskProtocol`, and `R0P.MaskD3Glue`: their available
objects are in old generic-cache roots, without a checked current overlay. The previously
missing `R0C.SemStatement` is present via `objects2`, but that object belongs
to the old `R0FS` chain. Before a refreshed semantic replay can be assessed,
the remaining transitive owners to inspect/refresh are `R0.OpeningAlgebra`,
`R0.BadSetBounds`, `R0.Binding`, `R0FS.Protocol`,
`R0FS.Hypotheses`, `R0FS.V2`, `R0C.SemStatement`, `R0P.SemD3Glue`,
`R0P.MaskProtocol`, and the mask-chain owners listed above. `Wide.SubfieldDescent`
has already been refreshed and audited in the frozen checkpoint. This
is an object-lineage inventory only; it does not say each rebuild is required
if an existing object can be shown to have been produced against the refreshed
dependency objects.

Root also reported a green combined `R1ReuseCheckpoint` after the current R0
opening path was compiled. That checkpoint does not establish that the three
old `R0P` semantic target objects were rebuilt; their hashes below remain the
older-cache hashes observed during this inventory.

## Current source SHA-256 inventory

The following hashes pin the source owners and downstream files named above.
Paths are repository-relative.

| Module | Source | SHA-256 |
|---|---|---|
| `R0.Dot` | `docs/research/v8-wide-reference-20261005/lean/R0/Dot.lean` | `9347df933fb49a436b98e25309980ff4f8939088ad11546ae537a16885bddf2f` |
| `R0.OpeningWeights` | `docs/research/v8-wide-reference-20261005/lean/R0/OpeningWeights.lean` | `44e2f004820cd0eb211fef5929b39cffa8bd359b4fa2455f9bad57de33a61199` |
| `R0.RoundNormalization` | `docs/research/v8-wide-reference-20261005/lean/R0/RoundNormalization.lean` | `af1a59d786104ba215c5c241c9ac7b32fff3c828b51456e6320522792584c0c4` |
| `R0.OpeningDefinitions` | `docs/research/v8-wide-reference-20261005/lean/R0/OpeningDefinitions.lean` | `fd3b3efc5dbcb7681dc54053a5caf7b8005f618fb7e2ad37c7c0764a6fa3da27` |
| `R0.ChordImage` | `docs/research/v8-wide-reference-20261005/lean/R0/ChordImage.lean` | `227b30a3343668da8ee9b4d19d732feacd1423615aba2462c00dca170a1c6a0e` |
| `R0.Chord` | `docs/research/v8-wide-reference-20261005/lean/R0/Chord.lean` | `ade2d0d7ccbaa66cac517578e8c4ead02b674d81fb1e2f1638f3746c2b01d189` |
| `R0.OpeningAlgebra` | `docs/research/v8-wide-reference-20261005/lean/R0/OpeningAlgebra.lean` | `4f36236f066acac2a4164174e5a7176a521bca0084c906d7e019bdc3d450a4a1` |
| `R0.BadSetBounds` | `docs/research/v8-wide-reference-20261005/lean/R0/BadSetBounds.lean` | `4e1110b8e1c5a02996ec19174ef399d8d9c49cb081cb405d76ad133ade433a22` |
| `R0.Binding` | `docs/research/v8-wide-reference-20261005/lean/R0/Binding.lean` | `b150fe57b04aba6f5f8a506f344c6e6a5b0d3269ceb2dcb1c58fe1cd5ecdae42` |
| `Wide.Cardinality` | `docs/research/v8-wide-reference-20261005/lean/Wide/Cardinality.lean` | `b45deda44a546a25123dabcaa04f3a2f66f6b585c8b81d3198f903ce85a7a2a2` |
| `Wide.JointList` | `docs/research/v8-wide-reference-20261005/lean/Wide/JointList.lean` | `22012dc039ceb0290a879962ed4940ce10c52d598d43e681e1ae4e96e358d259` |
| `Wide.SubfieldDescent` | `docs/research/v8-wide-reference-20261005/lean/Wide/SubfieldDescent.lean` | `a12a3c751a9b11ad1ee012c43a6f79317f14f051f3d949da1c89a605a0a6826d` |
| `Wide.SubfieldDescentCore` | `docs/research/v8-wide-reference-20261005/lean/Wide/SubfieldDescentCore.lean` | `8ceae54f6a0c3d695c63224aa9a52e45d34c1dbd4e278e11cee00ded061b4889` |
| `R0P.MessageDescent` | `docs/research/v8-r0-sem-proof-20261008/lean/R0P/MessageDescent.lean` | `79c8eae0dee9f4a094646b36ac44271d098a62a155008ff3b85549b9ac13be2c` |
| `R0P.SemD3Glue` | `docs/research/v8-r0-sem-proof-20261008/lean/R0P/SemD3Glue.lean` | `60830349937666ec050499c10bdb51e5c17811a949edd494f9205f0ee45ad852` |
| `R0P.MaskProtocol` | `docs/research/v8-r0-sem-proof-20261008/lean/R0P/MaskProtocol.lean` | `370faede24fa9a3afedb872da2d2e5843091d4653ad8a69f668d2facecc5aa5b` |
| `R0P.MaskD3Glue` | `docs/research/v8-r0-sem-proof-20261008/lean/R0P/MaskD3Glue.lean` | `7270ca471ad9d35a3db8ab279753df826f2d519bf626115fd4d39d825a303dab` |
| `R0P.MaskD2` | `docs/research/v8-r0-sem-proof-20261008/lean/R0P/MaskD2.lean` | `22af138da175023e657cd78ca98c15468b7c29ca166d5d14e3d02abb687e1041` |
| `R0P.MaskDuplexDecoder` | `docs/research/v8-r0-sem-proof-20261008/lean/R0P/MaskDuplexDecoder.lean` | `17b1b947a0e15271565d9c956aabaeccd5a9d3ce58ad75f4b0b6b63fd7aafc6c` |
| `R0P.MaskBadSets` | `docs/research/v8-r0-sem-proof-20261008/lean/R0P/MaskBadSets.lean` | `18b0499811001773be7ec5d2ff2e9463a2ff22048281595b76008033427862f7` |
| `R0P.MaskView` | `docs/research/v8-r0-sem-proof-20261008/lean/R0P/MaskView.lean` | `f27198834fa43256002cce83de7eeef675fecd88e89db0ee7a2bc00ef3a8b44b` |
| `R0P.MaskSource` | `docs/research/v8-r0-sem-proof-20261008/lean/R0P/MaskSource.lean` | `299712d96b2025176c6b959be149b1b546beda21e3c60d2fa8514c367a3e304d` |
| `R0P.MaskSemantics` | `docs/research/v8-r0-sem-proof-20261008/lean/R0P/MaskSemantics.lean` | `801ca30d6263bd352843a7f3198029860f742d4699ed2240e1c5556e5f3ce500` |
| `R0P.MaskPrefix` | `docs/research/v8-r0-sem-proof-20261008/lean/R0P/MaskPrefix.lean` | `4bbf715dd3c5cf4b1b8976ec81c3c657402369caab15b2f99fbc8fe3a40f52f5` |
| `R0P.MaskNoHit` | `docs/research/v8-r0-sem-proof-20261008/lean/R0P/MaskNoHit.lean` | `31ffcd813d6aa662dbe6b4de4e4251857332a92b49f1361eb138e6160e00b889` |
| `R0P.MaskEarly` | `docs/research/v8-r0-sem-proof-20261008/lean/R0P/MaskEarly.lean` | `d059910517c04de436fcaa20d0c67bcc4e59ae80715a71ac6ce25f7a892c98b7` |
| `R0C.SemStatement` | `docs/research/v8-r0-close-20261007/lean/R0C/SemStatement.lean` | `065e73821e28582b1e08073fb64383f0bec7342cf8fed0cbbe3bd68430fab90d` |
| `R0C.V3.R0Q` | `docs/research/v8-r0-close-20261007/lean/R0C/V3/R0Q.lean` | `e1bdb96a86c81b143c6962f904ccc2c4f291ec7f81dcdc0f54534cfa83ba0fb9` |
| `R0FS.Protocol` | `docs/research/v8-r0-fs-20261006/lean/R0FS/Protocol.lean` | `e3934ccf98f6578656e5c48cc6f3d5f6275808fa7778c197105227c09949a89c` |
| `R0FS.Hypotheses` | `docs/research/v8-r0-fs-20261006/lean/R0FS/Hypotheses.lean` | `937e18c5770da39b298dcfb7ff2d635e98069996ae18dc1c4158b28029ecb7b7` |
| `R0FS.V2` | `docs/research/v8-r0-fs-20261006/lean/R0FS/V2.lean` | `0a9ee117ea525400c1bd6ddf2725f084c929b6bba0e8164a0bbbf597a108f9c8` |

Current remote hashes of the older cached `.olean` objects for the three
semantic targets are `R0P.SemD3Glue`
`567bfa2b8ad2579721a0f6efb058d9545be94ff502d63ec4d9d5956cda5c754f`,
`R0P.MaskProtocol`
`bf3c5d48efb7eaca08388063be94b1c19cce61dd26e58ab93f391525e324127b`, and
`R0P.MaskD3Glue`
`6f196c2da75758772bccc3202677439139dfaa2a31ce060c281293c2fc7d77db`.
These hashes identify the cached objects observed in `objects2`; they do not
assert compatibility with the current sources.
