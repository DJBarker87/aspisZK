# Resumed admission refusals

36021: upload admission refused 2026-10-28 10:53:00.637803 UTC, exit 78,
allowed=false. Retried same ID at/after 10:56:25 UTC (over 180 s), passed.

36049: scope admission refused 2026-10-28 11:26:25.644103 UTC, exit 78,
allowed=false. Original admission and logs retained under refusal-36049-*.
Retried same ID after 11:29:33 UTC (over 180 s), passed.

36052: scope admission refused 2026-10-28 11:32:46.926205 UTC, exit 78,
allowed=false. No compiler started and neither 36052 nor subsequent queued
36053 was consumed. Same-ID retry must be after 11:35:46.926205 UTC.

These are resource contention, not proof errors, admissions or charged
compiler attempts. No scope was started while refused; no barrier was edited.
