# Ordered gates and budget reservation

Run 251 source vertices for FJp_Top, then RPu_FJp_TopAudit and
RPu_FJpKernelComparison (two audit contexts). Run the remaining 83 FJu source
vertices, then RPu_FJu_TopAudit and RPu_FJuKernelComparison.
With four query contexts, 334 source contexts consume 338 attempts.
Continue the FJv_Top dependency postorder until attempt 495. This leaves five
batches for every freshly compiled source context (100 contexts per batch).
If all pass, 491 fresh source contexts + four root/statement audit contexts +
five declaration audit contexts = 500 attempts. No attempt is a package replay.
Every compiler invocation remains a separate module in its own admitted scope.

All 1496 union snapshots are committed to make the remaining source frontier
reviewable; their mere presence never implies successful compilation. Each
root's actual checked header must agree with its planned selected import graph.
FJv root booking remains blocked until all of its missing dependencies and its
own fresh top/type/axiom/reachability audits pass. A smaller pending frontier
is continuation evidence, not closure credit.
