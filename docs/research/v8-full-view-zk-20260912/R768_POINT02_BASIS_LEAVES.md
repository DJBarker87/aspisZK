# R768 p0/p2 candidate basis leaves: focused proof status

This scratch prototype proves exact ordered ten-factor expressions for the source-shaped basis at original index 993 and the remaining 99 candidate indices from the R762 inventory. There are 200 declarations total (100 indices × p0/p2), in independent focused chunks of at most 32 declarations. It does not evaluate products in a concrete field and proves no product nonzero, transport, 343-gather composition, source execution, privacy, or security statement.

Each theorem rewrites the exact existing `points0_exact` or `points2_exact` theorem, unfolds the ten source factors and uses commutative-ring normalization only to align the explicit ordered product. Every declaration prints its axiom dependencies; the reports contain only `propext`, `Classical.choice`, and `Quot.sound`. The first failed prototype is retained as a changed-target attempt; after adding symbolic `ring` normalization the single-index prototype compiled. The following seven chunks all compiled green.

The target index set is the 99 candidates remaining after index 993, in R762 inventory order. Generator and chunk checksums are in `manifest.json`; full source snapshots, logs, receipts, and every axiom line are linked by `attempt-manifest.json`.

| Target | Exit | Wall | Peak RSS KiB | Swap | Axiom reports | Source SHA-256 | Receipt |
|---|---:|---:|---:|---:|---:|---|---|
| `AspisV8R19/R768Point02BasisLeaves.lean` | 1 | 0:01.49 | 2311144 | 0 | 2 | `690eb24a1d3701f58cfb3a06bf122d965965d50c4babf38c4bb45bb5d27f7e57` | `aspis-focus-1791147919833640000.receipt.json` |
| `AspisV8R19/R768Point02BasisLeaves.lean` | 0 | 0:01.54 | 2327680 | 0 | 2 | `a370710bbb6b6b028dd664c2a5be5dee5fef31bc71f5c5816bedd3258b7d217a` | `aspis-focus-1791147935028062000.receipt.json` |
| `AspisV8R19/R768Point02LeavesChunk00.lean` | 0 | 0:13.36 | 2372088 | 0 | 32 | `727bcfe45bcb651d0fc37cb28f9c78c3f00c469e076a77f1cd635c5743898d19` | `aspis-focus-1791148004813321000.receipt.json` |
| `AspisV8R19/R768Point02LeavesChunk01.lean` | 0 | 0:13.14 | 2373728 | 0 | 32 | `67997df63efeaac15d4347bcc8ff29f58272a41f186c1c5432ee37ccd83641de` | `aspis-focus-1791148029368814000.receipt.json` |
| `AspisV8R19/R768Point02LeavesChunk02.lean` | 0 | 0:13.14 | 2372392 | 0 | 32 | `f15466ed4bc712676e3e7fe3b05337270e7b7dc278cde1e509333050c04a6637` | `aspis-focus-1791148048255322000.receipt.json` |
| `AspisV8R19/R768Point02LeavesChunk03.lean` | 0 | 0:13.29 | 2372976 | 0 | 32 | `082ccbeb74c71e1118084f689c49766b12ea90d2305183a1f31ba1518cde6f70` | `aspis-focus-1791148067005016000.receipt.json` |
| `AspisV8R19/R768Point02LeavesChunk04.lean` | 0 | 0:13.64 | 2375544 | 0 | 32 | `c668c186d8e7e663ab358192a906c1fd9507cacce347faa5043cfc28abc48905` | `aspis-focus-1791148085737128000.receipt.json` |
| `AspisV8R19/R768Point02LeavesChunk05.lean` | 0 | 0:13.01 | 2374740 | 0 | 32 | `2ca879220c7265e030754a78a2a58402333987b0f30bd9b6a3f5b25b7fdf0f1d` | `aspis-focus-1791148110456900000.receipt.json` |
| `AspisV8R19/R768Point02LeavesChunk06.lean` | 0 | 0:03.28 | 2331972 | 0 | 6 | `4ece3abf2846f4e043feae422f3146c964296b843e962032478fe814728d690f` | `aspis-focus-1791148129474893000.receipt.json` |

First remaining proposition: bind the proved pivot-zero transport of both fixed points to all 519 required positions and consume the resulting leaves in the 343 generic gathers. These 200 identities alone do not prove field nonzeroness, the full source matrix, native execution, legal witness compatibility, oracle law, privacy or soundness. Verifier results and security parameters unchanged.
