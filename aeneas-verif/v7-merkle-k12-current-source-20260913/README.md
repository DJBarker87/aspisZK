# V7 current-source K1.2 Merkle bridge

This bundle refreshes the four-function V7 Merkle bridge against production
`main` commit `8a830f7fbfb622cc8167b8cad1057e43b9003d62` (tree
`a57ac60267181982affb09175ffe22b147fd5423`).  Its Charon LLBC is
`extraction/V7MerkleK12.llbc`, SHA-256
`f165888fcef1f8886ee5e7acec7841274f9c60b291e2b6c83be497430bd934db`.

The Aeneas executable was rebuilt from the frozen d860 source plus the three
existing result-aware patches.  It was accepted only after matching both:

- version: `aeneas d860ac47-patched-result-aware`
- SHA-256: `87f65bd36e0dad06d322f833fcb4cb6c3e7d84acf149b31d0c4e61656d23ea4a`

The raw translation is deterministically normalized by
`toolchain/aeneas-failure-diagnostic-normalization.patch`.  The patch replaces
only Aeneas's proof-carrying diagnostic string passed to `Result.expect` in
the statically successful 32-to-26-byte truncation.  It does not change the
source digest, array conversion, hash call, node traversal, or any accepted
result.  Without this overlay, Lean's generated string proof introduces a
`native_decide` axiom; the normalized replay does not.

Focused replay compiled the generated modules and
`proof/V7MerkleK12SourceBridge.lean` on the NUC under
`MemoryHigh=4G`, `MemoryMax=6G`, and `MemorySwapMax=0`.  Peak memory was
437.9 MiB; swap was zero.  Every printed bridge theorem depended only on
`propext`, `Classical.choice`, and `Quot.sound`.

This proves the current low-level 208-bit Merkle source model.  It is not yet
the production-caller bridge, the K1.3 pre-query-view bridge, or the full
K1.2--K1.6 security composition.
