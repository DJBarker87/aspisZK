Stage 5: terminal cuts and same-owner composition

K096/K097 certify the two deployed range lengths and their scalar control.
K098–K100 check exact std MaybeUninit five-element finalization and matched
reply/argument controls. K101–K106 check ordinary early Query rejection after
initialized arbitrary prefixes for capacities50/60, retaining the borrowed
query pointer/value frame; reply and frame controls fail. K107/K108 are exact
current-source KMX controls. These do not certify allocator internals or
empty panic I/O. Scratch-only cfg(kani) array-assume-init feature is recorded
in NFB_ARRAY_FEATURE.patch; shipped files remain unchanged.

L041 derives exact actual-emitted continuation/failure cuts. L043 and L044
associate one physical two-owner gather trace, all its query-frame prefixes,
and SAME terminal buffers with the actual root. L045 obtains every terminal
prefix/product/inverse/resize/reverse/map/collect result from ONE accepted
terminal call. L047 derives reverse write traces and exact inverse-owner
payloads; L048 proves guard-local initialized payload and final publication
from per-slot observations. L050 proves cursor bounds and that a successful
terminal must exhaust the original query view. All accepted theorem axioms
are standard. L042,L046,L049,L051 failed locally and are excluded.

A stale-dependent preflight was rejected before launching L050; the driver
correctly prevented use of failed L049. The numbered L050 host run was then
used for the repaired smallest predecessor. No failed host attempt was
resubmitted. Terminal/root assembly and validator are still OPEN.
