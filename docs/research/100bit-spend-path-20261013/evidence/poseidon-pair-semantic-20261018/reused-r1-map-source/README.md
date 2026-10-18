# Accepted algebra-map owner alternative

The exact expected module `PoseidonMap.olean` was not found in the searched NUC project-offloads roots, pinned consolidation tree, or the local `/Users/dominic/ZK` workspace. The closest accepted owner is `R1PoseidonMap`.

`R1PoseidonMap` exports the namespace `AspisR1.PoseidonMap` with `State`, `mapState`, `map_poseidonExternalLinear`, `map_poseidonFullRound`, `map_poseidonInternalRound`, and map lemmas for external-initial/final and internal constants. Its source imports only `R0P.Semantics`, so the exact direct import source/object are staged under `imports/R0P/`.

Accepted NUC attempt h:
- source SHA: `120f34445bece1c624f6094d4b6f32d36e091366faf5c22a26fdeca2a2030a40`
- object SHA: `e54ff95b926e6f12bb61b469a936cb996f065e7fee97378ba1312ed041870ad7`
- receipt: `R1PoseidonMap-h.receipt.json` (receipt SHA `2fc1bf45bff94df37d910b498610e9d01eb43e5cd9c5306a33e29f8c7eca2c36`)
- exit 0, 4.84 s, peak RSS 3,389,472 KiB, swap 0, `MemoryHigh=4G`, `MemoryMax=6G`, `MemorySwapMax=0`.

Pinned direct import `R0P.Semantics`:
- source SHA: `9309c5faa3de30d4f35bfe46509fe335a821d89a43051201a97232c0b89dc615`
- object SHA: `0698eb3698a4aaaf2c5b65b12499863eea04b8d8483b1f3d04f7273ed3870f63`
- NUC source owner: `/home/dombarker/project-offloads/aspis-fs-generic-20261006`; its object was a symlink to that workspace.

This is an alternative module name, not proof that the missing exact `PoseidonMap` object is present. The Mac focused compile of source hash `120f34445…` has also been reported green by root as object `c51d1851…`; no additional compile is run here.
