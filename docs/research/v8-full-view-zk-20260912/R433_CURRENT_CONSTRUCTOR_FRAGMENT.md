# R433: captured constructor operation fragment

R433 proves that an explicit interpretation of the captured iterator constructor sequence equals R432’s iterator construction model. The source-operation table was checked against the frozen R431 capture. This is a fragment-model proof, not a Rust/LLBC execution, ABI, memory, lifetime or aliasing theorem. It does not close privacy or soundness.

## Verification

Exact target: `AspisV8R19/R433ConstructorFragment.lean`. Source revision: `7eb0fa2e7cc429a027e5e19f8460ccd22d162ea0`. The promoted bytes equal successful attempt B, SHA256 `816ea0b20355bcd23d06b0831841db279a08caa78cc59819abfebbb1fc04e2ef`.

Attempt B exited 0 in 6.80 seconds, GNU peak RSS 2,572,216 KiB, swaps 0. Terminal cgroup peak was 355,782,656 bytes, swap peak 0, with no OOM events. Both measurements are retained separately; the saved records do not explain their difference. It used pinned Lean 4.32.0 commit `8c9756b28d64dab099da31a4c09229a9e6a2ef35`, cached workspace, `lake env lean -j1 -M4500`, MemoryHigh=5 GiB, MemoryMax=7 GiB, MemorySwapMax=0, TasksMax=128.

All four complete `#print axioms` reports are in the successful log and receipt. `constructor86` has no axioms; `constructor_fragment`, `constructor_empty` and `constructor_backed` use only `propext`, `Classical.choice` and `Quot.sound`. Attempt A failed termination checking and its rejected output included `sorryAx`; its source, error and metrics are preserved. B fixes structural recursion by making separate calls on the branch children. The successful check was not rerun.

## Proved boundary and source table

The interpretation retains all 28 top-level statements and both branch arms: prefix18, true1, false7, tail9. It represents metadata, seven casts, pointer offset, storage operations, the marker move into the iterator aggregate, and return control. It uses R430’s explicit constant fragment and R432’s explicit pointer fragment. Unsupported operations return `None`, which is not asserted to be a Rust error. Both arms are represented; the modeled selected QM31 constant chooses the nonzero-size arm.

Within these rules, `constructor_fragment` proves equality to `newIter` for arbitrary modeled heap, pointer and length, including unsupported outcomes. The other theorems preserve the empty/dangling construction and establish start/end values for bounded modeled storage. Cast and metadata rules are explicit representation choices; the theorem does not prove their Rust ABI semantics or validity. The fixed heap is not a source frame proof.

The strict structural checker passed against R431 LLBC SHA256 `df9180ee7c9959a7840d6edac0b756f007ef33ed0bd88bb36faf57a3e18f2358`, checking command lists, native operands/types, metadata projections, global31, offset and aggregate copies/move. The R429-to-R431 constant graph comparison is equal after precisely renaming functions142/145/153 to143/146/154, resolving hash-consed types, and removing documented span/statement metadata; global31/32 remain unchanged. Normalized graph SHA256: `a5d0602a85bb1bfe5f84c66c8fe2441b3a90173c3d141398ba1ad6725caae23d`. These are executable structural audits, not kernel source-semantics theorems.

## First remaining proposition

Justify source value images and primitive ABI/cast/metadata/pointer correspondence, including valid shared slices and empty cases. Bind actual fold70 with pointer loads, unchecked successor safety, captured mutable-power restoration, storage frame, and complete check/drop/unwind/error behavior. R193 and R432 supply model loop/load results but do not close this actual-source bridge. Vec::extend remains separate.

Whole freeze and inverse Domain behavior, complete callback/oracle chronology, universal joint C1/H1/G compatibility including p0/p2 and adaptive/degenerate prefixes, the entire published-view simulator and shared-oracle probability losses, coherent pre-beta quotient extraction, and optimized-to-source acceptance remain open. Genuine 999,790 / 999,532 CU and all security parameters are preserved. No benchmark, unchanged regression, deployment, merge, transaction or wallet operation occurred.
