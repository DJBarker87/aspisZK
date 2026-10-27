# Third library pass

Base 7aebfd030c; authorized IDs 41588–41799 (srcid8 tail, never reused).
100 Lean attempts and 6 bounded control/copy Kani runs. Last three charged
Lean attempts use reserved IDs 41797–41799. No field-arithmetic Kani.

First test byte-carrier references for op26/30/31 and a borrowed Vec-update
reference for op33; inspect op36 loan/destruction paths without suppressing
preflight. Preserve op32's allocator-effect deferral. Native bounds, source
extraction toolchain and deployed association stay explicit.

Then split the SHA block composition at symbolic stage boundaries; use
already checked schedule/round/feed-forward equalities rather than evaluate
concrete arithmetic. New modules only, PV_CBL_ prefix. Final audit follows
focused closure; unchanged repository-wide regressions are not repeated.

Dispatcher packet is a proposal only. No deployed build/configuration is
changed; isolated release microbenchmarks may compare the pinned soft and
runtime-dispatched implementations. Never add an intrinsic premise to T.
