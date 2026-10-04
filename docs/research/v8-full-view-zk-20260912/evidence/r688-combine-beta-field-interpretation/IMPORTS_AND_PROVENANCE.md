# Imports and local matrix-definition provenance

The final R688 target directly imports `AspisV8R19.R687CombineBetaComposition` (SHA-256 `ca7871b65858bcaf3af6ea5cf70f0c16118140d924dcaaa04564a616de4d3b67`), copied here as `dependencies-R687CombineBetaComposition.lean`.

R688 cannot import `AspisV8R19.R620MatrixAction`: R620 imports generated R618 types while R688 imports R614 types, and the first focused R688 attempt (`1791121871180874000`) records the duplicate generated declaration collision. R688 therefore copies only R620's mathematical `matrixCoordinate` and `matrixAction` definitions over the R614 generated arrays. It does not import, invoke, or claim R620's native matrix-execution theorem. The inspected source provenance is copied as `provenance-R620MatrixAction.lean` (SHA-256 `136002d73ff7d1ff257c937966677280f66f2de49b65fd1b706058a0897c8f59`).

This is a representation adaptation required by incompatible generated type environments, not a source-execution correspondence argument.
