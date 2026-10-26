# Stage 3: reached semantic log and preparation buffers

UNADOPTED frozen3 candidate; S2 open; target not yet established.

F3R_VerifyLog.log derives the complete actual semantic-code ordered log:
public initializer, all25 source semantic rows, and both circle calls, from
that code's acceptance. F3R_TraceUnique.unique identifies the log and final
state of two same-start/same-row source traces, retaining explicit row bounds.
F3R_PrepareBuffers.reached strengthens the existing reached preparation split
with its actual compact slices, expansions and recombined buffers. Both
buffer-length laws are explicit and will be discharged at the installed
native instance, as in PAln_BothBuffers. No model acceptance or desired final
log equality is assumed.

57/100 actual Lean invocations;0/0 Kani. F3R_039 hit the default heartbeat
limit in the monolithic semantic-finish proof and is excluded. Its continuation
was isolated as F3R_FinishTailCode/F3R_FinishTail; the changed split compiled
in044. No limit was raised and no unchanged timed-out source was rerun.
All final top theorems so far audit only accepted standard axioms; failed
recovery sorryAx lines are excluded. Exact attempt metadata and snapshots
are retained. No package replay, shipped changes, artifact rebuild, key
operation or push. This stage closes local log/buffer facts, not the final
native pair join or composed non-vacuity.
