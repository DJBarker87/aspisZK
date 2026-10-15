# Public option-shape Lean target

This bundle preserves the four focused attempts for Lean module `PublicOptionShape`: attempts a–c failed during proof development and attempt d compiled successfully. The final source defines an executable `check` equivalent to the `canonical` option/variant predicate and proves the constructor-shape lemmas. It does not parse Rust bytes or impose numeric bounds.

The green receipt is for target `PublicOptionShape`; the compiled object is `objects/PublicOptionShape.olean`. It is the correct module identity for imports of `PublicOptionShape`. The source declares namespace `AspisR1.PublicOptionShape`.

Attempt d: exit 0, 1.76 s wall time, 3,311,504 KiB maximum RSS, zero swap; `MemoryHigh=4G`, `MemoryMax=6G`, `MemorySwapMax=0`, `TasksMax=128`. The five public `#print axioms` reports are `[propext, Quot.sound]`.

The direct import is `R0P.Core`. Its current authoritative repository source is included under `sources/R0P/Core.lean` with its source path and hash in the manifest. The focused workspace resolved the compiled import through the pinned `LEAN_PATH` cache at `/home/dombarker/project-offloads/aspis-fs-generic-20261006/objects/R0P/Core.olean` (hash recorded in the manifest); the source was not present in the focused workspace's `sources/` directory. This records the cache object provenance without claiming that the included source file was the exact source used to produce that object.
