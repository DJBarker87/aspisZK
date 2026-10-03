# R440 fixture and patch audit

Read-only checks of the compiler-created closure fixture and the local translator candidate. No build or execution was performed.

The candidate is byte-for-byte the pinned original after removal of the one exact three-line monomorphize early-return block; closure binder construction and method insertion remain. The fixture text includes mutable `power`, shared `gamma`, generic `FnMut(u32, &u32) -> u32` invocation, returning the updated power, and direct multiplication/addition. This only describes fixture coverage; it is not the verifier and proves no source execution correspondence.

See `audit.json` for hashes and mechanical checks.
