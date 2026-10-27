# Own scheduling deviation and repair

During expansion work LPl_L047 was mistakenly launched while LPl_K013 still
ran. Both were individually admitted/capped, but this violated the binding
one-scope-at-a-time rule for this job. The Lean scope finished before the
mistake was observed; host process inspection then showed only K013 active.
No other job was signalled or killed, no cap was raised, and shared host
infrastructure was not changed. The failed Lean proof output is retained and
not accepted evidence. The exact journal events are in LPl_SCOPE_OVERLAP.log: K013 started
16:53:07.231139UTC; L047 started16:53:36.629686UTC and ended by
16:53:37.847439UTC; K013 ended16:54:39.493272UTC. The Lean scope
overlapped for approximately1.218s. Receipts separately record wall/RSS/caps.

Repair to OWN LPl_attempt.py: before any reservation/upload/launch, refuse if
any earlier own attempt configuration lacks a terminal receipt, and check the
host for active own S2W runner processes. This is an own orchestration guard,
not a repair to a shared launcher/admission/monitor. All subsequent scopes must
be serial. Final verification reports this deviation instead of falsely
claiming the entire job was serial.
