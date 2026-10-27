# Complete fixed-table transfer timeout

The third Kani run (number9) timed out after1800.276s, exit124, peak RSS6663659520 bytes, swap0. It compared all15 RW and5 RP fields, with no stubs, against the exact owned reference at the independently pinned root table. The full shipped21-step helper still executed. No failed assertion or ROW counterexample was reported. The scope is inactive and its terminal receipt is retained. It is not rerun unchanged.
