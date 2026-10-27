# Resource preflight

All actual proof/checkpoint buffers remain behind named structural window pins.
Each decoder uses one32-byte array plus the generic parser equivalence. No
whole-buffer evaluation is used. The final-round polynomial is split into
14 named Horner steps, each one native wide multiplication and one native wide
addition; the largest arithmetic node is a fixed8-limb field operation, not an
unfolded recurrence. Explicit Python words are generator outputs only; Lean
checks every native call. Native arithmetic is evaluated only on these small
constant cells. Full polynomial joins consume named calls in source order.

Weight construction similarly separates ten reverse successor cells and
25 four-value factor cells. Native loops will be closed by a named finite
transition induction and computed body calls; no full recurrence reduction.
The initial generic arithmetic preflight023 passes, exit0, wall4.096783156s,
RSS5921580KiB,swap0. No caps/depth/heartbeats changed; no resource-killed or
unchanged timed-out job has been rerun. Exact per-attempt fields in receipts.
