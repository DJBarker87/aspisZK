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

## D-4: index assignment is once per row, not once per copied byte

The native byte-window drafts are split before launch: byte-only windows
frame the entire index array. A separate parent-read/index-write gate handles
the once-per-row index store. Recomputing parent and writing idx[w] on every
byte would be wrong when w=i, repeatedly halving the source cell. No such
composition is claimed. NBY_RowCopy only composes the value-byte plane; its
source reply is fixed for that copy. The joint index/one-byte gate is a local
cut, not a32-iteration implementation of the original row.

## D-5: negative trace size

K080 solves SAT but fails to produce a terminal counterexample before the outer240s deadline. It is not a successful control. Its replacement isolates a single last-byte sentinel on a fixed full carrier, with the SAME slot helper/predicate, exact KMX patch, frozen graph and verifier flags. This changes the failing witness representation rather than rerunning the huge arbitrary-array trace or raising a limit. K079 stays uncredited unless that new control actually fails.
