# QueryResidualBridge focused checks

Attempts a, b and c are successive source extensions and all exited zero.
The final target is R1QueryResidualBridge, attempt c, SHA-256
`392317ece75d5d7b29d034d4425ffb4e95e52b71078e70317339b40fbf1b4aad`.
It compiled in 1.51 seconds with 3,147,460 KiB peak RSS and zero swap under
MemoryHigh=4G, MemoryMax=6G and MemorySwapMax=0. All seven printed axiom lists
are `[propext, Classical.choice, Quot.sound]`. There is one harmless linter
warning about an unused Fintype section parameter, retained in the log.

The final theorem consumes the explicitly defined 22-step field accumulator,
first-fold checks and existing binding premises. It concludes query membership
in the fixed matching support of size at most 9557 outside the rho exception.
It does not assert Rust, checkpoint, semantic or shared-oracle correspondence.
See the adjacent query-chain manifest for exact source/receipt validation and
base revision. No unchanged target or full package regression was repeated.
