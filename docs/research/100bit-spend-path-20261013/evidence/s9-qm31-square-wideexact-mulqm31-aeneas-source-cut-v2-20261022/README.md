# S9 QM31 square and WideExact mixed multiply Aeneas source cut

This is a fresh source-only packet extending the Charon cut with the existing pinned Aeneas binary. It includes the generated Lean `Types.lean` and `Funs.lean` source files plus translation metadata; it includes no raw LLBC or compiled objects. Charon’s raw LLBC remains on the NUC and is pinned by SHA in the manifest.

The generated output contains nonopaque definitions for the exact pinned `QM31.square` (source line 951) and `WideExact.mul_qm31` (source line 178), and 17 generated functions whose sources are `field.rs` or `wide_exact.rs`; all are nonopaque. Both reachability shims are generated as functions. The original `field.rs` and `wide_exact.rs` source snapshots are byte-identical to their prior pins.

Aeneas ran under a fresh common-admission scope with `MemoryHigh=2 GiB`, `MemoryMax=4 GiB`, `MemorySwapMax=0`; admission passed at 32.375 GiB finite reservations. Aeneas itself exited 0 in 0.301 s (RSS 71,984 KiB, cgroup peak 71,266,304 bytes, swap 0). The first runner exited 1 only after translation because its validator searched for fully qualified Lean declaration names, while Aeneas writes relative names inside the namespace. That post-run check failure is retained in `validation-correction.json`; a corrected independent check passes against the already-generated files, with no Aeneas rerun.

This packet establishes successful source translation and nonopacity. It does not claim a Lean compilation or source-to-Lean refinement theorem. Run `python3 check_packet.py` to verify the packet.
