# R434 current actual fold guards: source evidence

This package preserves the R434 diagnostic LLBC extraction and its command, launch/collection receipts, raw logs, independent audit, helper inventory, and the mechanical Fun70 and closure inventories. The LLBC is stored losslessly as deterministic gzip; `materialize.py` verifies and restores the exact original bytes into a fresh directory. `source/relation_callback.rs` is the frozen full Rust file corresponding to the recorded hash. `base-r431/r429-command.snapshot.json` supplies the predecessor command snapshot referenced by the R434 scope receipt.

The capture reports Charon exit 0, LLBC `has_errors=false`, 13.79 s GNU wall time, 630388 KiB GNU peak RSS, zero swap, and a terminal cgroup peak of 494043136 bytes under memory.high 5368709120, memory.max 7516192768, memory.swap.max 0, pids.max 128. GNU RSS and cgroup peak are distinct measurements. The saved independent audit records the exact two added helper includes and fresh destination relative to R431, with frozen source hashes unchanged.

This is source/LLBC evidence only. Formal axioms are not applicable; no proof of source execution correspondence, pointer safety, or release/security property is claimed.
