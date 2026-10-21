# S8 continuation

Stage 1: three local base/step/exit Kani roots pass (`kani2-04`). This first
preflight is bounded to destination prefixes of length at most three; it is
not an arbitrary-length frozen traversal claim. The step uses the real
`IterMut::next` on an unconsumed suffix, the literal shipped body, and the
owned reducer. No reducer stub. All raw lanes are symbolic U64. Failed CLI,
workspace bootstrap and memcmp-unwinding attempts are retained (01–03).

Lean finite-step induction and production-size step are in progress. No
headline premise removed and no frozen whole-loop timeout rerun.
