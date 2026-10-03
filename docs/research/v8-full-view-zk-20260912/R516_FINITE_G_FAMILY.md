# R516 finite G-family preservation

The final compiled theorem establishes that arbitrary weighted sums of the 13 selected source-shaped G directions preserve inactive balance and all 271 mixed-coin values. Adding one of these directions to any supplied G table preserves the mixed coins; balance is preserved when the supplied table is balanced. Roots and coefficients remain unrestricted.

Target: `AspisV8R19/R516FiniteGFamily.lean`; source revision `1caad4fb9ba028a51ccf3aa742a4d65fdff010e4`; SHA-256 `82ca398eb89e769cb3b145abb77e3f232cacc9503e45fb6ed48bb39d50ea1155`. Run `1791054461238562000` exited 0 in 0.98 s; peak Lean-child RSS 2,297,900 KiB; swap 0. It used pinned Lean 4.32, `-j1 -M4500`, MemoryHigh=5G, MemoryMax=7G, MemorySwapMax=0, TasksMax=128. All four complete `#print axioms` outputs contain only `[propext, Classical.choice, Quot.sound]`.

This is algebraic preservation for the stated finite family, not universal joint C1/H1/G target coverage or source execution. The first remaining work is that coverage proof and actual whole-prover Rust execution, followed by simulation/probability and soundness. Full end-to-end privacy and security are not proved.
