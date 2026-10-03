# R494 parser iterator capture

This archive preserves the successful selected LLBC capture, its exact command
and receipt, and complete stdout/stderr records for both preceding failed
attempts. `r494-result.json` pins source revision
`4f2f2f13a55425cedb2cdc19cfcf2780edbb8b35`, the nine source-file hashes, the
captured LLBC SHA-256
`15719568de8a064beeb48717de9bdeb003bb9e185054c09eb5a07c6196a4147e`, and
the successful retry-2 measurement: exit 0, wall time 0:13.27, peak RSS
626,428 KiB, zero swap.

The initial attempt exited 200 before Charon started because its working
directory was absent. Retry 1 exited 101 with the pinned configuration flags
omitted; it produced no LLBC. The final retry used the recorded pinned flags
and captured the LLBC. This is diagnostic extraction only; it is not a Lean
proof or a source-correctness result.
