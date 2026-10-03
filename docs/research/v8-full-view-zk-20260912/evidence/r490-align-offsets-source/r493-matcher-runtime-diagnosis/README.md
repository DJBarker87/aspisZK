# R493 matcher runtime diagnosis

This archive preserves the focused runtime probe that found the selected
concrete source name `core::slice::{[u8]}::len<u8>` and established that the
generic matcher aliases did not classify it. `MATCHER_DIAGNOSTIC.md`, the probe
source, selected LLBC, and complete raw probe logs are retained unchanged.

The diagnosis identifies a concrete translator matcher route only. It is not a
Lean proof or a source-correctness result.
