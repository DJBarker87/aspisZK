# Process deviations and corrections

Read-only status SSH queries were issued while a submitted launcher SSH connection remained active. This violated local-lean rule10b's prohibition on extra parallel SSH sessions. No process was resubmitted, no second capped scope ran, no host infrastructure or shared source/object was modified, and no proof credit derives from those queries. Discontinued; subsequent recovery uses the serial wrapper after submission returns.

The initial own queue proceeded from a timed-out positive to a different inverted/diagnostic control (K024→K025 and K026→K027). These were different assertions, not unchanged timeout reruns; neither gives credit to its timed-out positive. The queue was strengthened to stop on timeout/kill. The K028 pause occurred before admission/submission; its stale own active marker was reconciled explicitly in NCH_QUEUE_PAUSE.json.

Lean failed drafts L003/L004 are not credited. L004 printed sorryAx because elaboration failed; corrected L005 is the accepted, standard-axiom result. No admitted proof, axiom, native_decide, heartbeat/depth override or unproved successful return was introduced.

A null()/null_mut() initializer typo caused four own compile failures K066–K069 because the queue originally stopped only on timeouts/kills. Corrected the initializer and made compiler failure a queue stop as well. K070 recovered the four planned targets in one serial multi-harness invocation, with both positives passing and both negative controls failing. Budget units are explicit:70 cargo-kani invocations,73 harness selections; no additional invocation was hidden.
