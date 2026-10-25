# Native constructor/claim with actual field decoder — candidate

The next native source-control target executes the real `weights::field`
32-byte decoder within the original Prepared::new/prepared_claim run.
The existing field hook retains its pointer/length/index/order observations,
then calls a name-only copy of the exact frozen source body, compares all
returned native coordinates against the input record and returns that actual
value. The arbitrary decoder return is removed. Nine Kani instrumentation
stubs remain, but only eight have normal-return primitive semantics cuts.

This changes the harness domain explicitly: the old harness allowed all928
bytes independently of the field reply tape. This candidate physically encodes
all29 arbitrary canonical native eight-word records into the same928-byte
payload before constructing View. It covers that canonical payload domain;
it is not an unrestricted malformed-input totality claim or an unconditional
weakening of the old theorem. Consumption of the checked caller's same-payload
canonicality remains required. No production source changed.

Local smallest-target compilation for `prepared_new_claim_point_6`:
v1 failed E0506 (the harness populated y1 after borrowing it into View),
3.840972417s/RSS687751168B/swap0. The source fix constructs View after encoding.
v2 passed1.120638750s/RSS537837568B/swap0, no solver launched. Both retain exact
source/tool/import/command/pre-post pins in their source-only receipts. A fresh
109-file source reconstruction matches every NUC input hash. These are compile
and reconstruction results, not a passing native verification.

The new owned NUC job waits for the existing claim partition queue to terminate,
then requests fresh admission for one24GiB/no-swap focused check. It does not
restart any existing process. Compilation then one native full-success SAT
check are expected; no certificate/elimination or full Lean replay is involved.
A failed predecessor partition does not become an assumption of this check.

The complete selected native bodies/carriers retain historical25866 context.
Current whole4bb3 source/dependency/artifact transport is not inferred; consult
S126-FREEZE-RECONCILIATION-20261025.md. Eight primitive cuts, native allocation,
initialization, SDK/std/runtime/extraction, oracle and release joins remain
open. Kani/compile results have #print axioms N/A and add no Lean axiom.
S1/S6 and the per-attempt soundness target remain unestablished.
