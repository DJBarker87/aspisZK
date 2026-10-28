# Scope findings

## D-1: instrumentation clock is not the global oracle prefix

Row/leaf/NoHash probes initialize a local Cell counter with prior<1000 to
avoid overflowing their instrumentation. This is not a property established
for an arbitrary adversary's complete oracle history. Consequently their
local one-call/no-call conclusions are kept in that instrumentation domain;
they are NOT a native full-history refinement. Interpreting that condition
as an actual global-prefix bound would violate the caller-domain ruling.
No such bound is added to RPx, L154 or a bridge premise. Source scratch/byte
properties remain their stated local properties; global chronological transport
is OPEN and must use an actual runtime-history association and same-carrier
induction, rather than that numerical clock restriction.

## D-2: fixed node backing is not the actual slice length

Early unlaunched row drafts used a96-byte/fixed-capacity physical node view.
Actual callers supply variable32*count slices. They are not credited. The
refined short-rejection gate quantifies length<=5504 and cursor; the supplied
write drafts also quantify actual length. K025/026 validate the short case;
they do not establish a successful supplied write.

## D-3: diagnostic traversals are not single-iteration certificates

K009/010 traverse a binary group's small inner loop. K011/012 traverse complete
admission. They are retained as diagnostic positive/control results, not P6
closure under the single-iteration ruling. NBI_CountScan/NBI_Admission and
NBJ_CountRows/CountLevels are imported; NBY_CountExecution proves the reached
bound on that existing execution, without replacing the missing native instance.
