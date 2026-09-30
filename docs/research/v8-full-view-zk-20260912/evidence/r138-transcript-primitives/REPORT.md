# R138 evidence report

The exact focused target is
`AspisV8R19/R137TranscriptPrimitiveBridge.lean`.  It was compiled on the
dedicated Linux host with Lean 4.32.0, `-j1 -M4500`, `MemoryHigh=5G`,
`MemoryMax=7G`, `MemorySwapMax=0`, and `TasksMax=128`.

Result: exit 0, 3.46 seconds wall time, 3,734,832 KiB peak RSS, zero swap.  The
printed axioms for every audited declaration are only `propext`,
`Classical.choice`, and `Quot.sound`.

The extraction-only Rust probe ran under the optimized release profile and
passed four tests.  It checks short and long flattening, all actual callback
payload widths, the 158-byte branch threshold, and the four compact-relation
round payloads.  It does not modify or replace production verifier code.

The packed branch's final hash address now compiles in Lean using named
symbolic lemmas for the scratch prefix and range writes.  The next open leaf is
the exact R137 QM31 sampler's wrapping-index correspondence for the bounded
0--8 cursor range; the Rust probe is not a substitute for that theorem.
