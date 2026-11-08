# Final aggregation review after SPEC-C17

Audit55494 was intentionally stopped on source/specification review, not memory
pressure: exit241;294.55s;peak7002088KiB;swap0. Its167 retained partial graphs
are archived without a pass. All focused semantic predecessors passed in
under7s each. There is no large numeral/recurrence reduction in this gate;
work is structural dependency traversal and constructor-summary comparison.

The corrected final input has532 declared roots in63 logical modules. At the
observed partial rate the full traversal is about16 minutes. Split it into
three disjoint sequential partitions178/178/176, each in a separate Lean
process with the SAME600s timeout and -M7000. ONE audit attempt55495 holds ONE
systemd scope for the three sequential processes. Aggregate driver timeout is
1200s; this sums three predecessor-validated graph aggregations, not a longer
Lean proof timeout. MemoryHigh6G, MemoryMax8G, swap0 and Tasks64 are unchanged.
No parallel Lean process or scope is introduced. Admission and the standalone
turn remain required. Review at10 minutes using partition/root progress and
RSS before continuing; no memory-cap increase is authorized or performed.

The private importAll collector suffix and raw walker are unchanged. ONLY
module/root arrays are partitioned. All532 roots, including preliminary
superseded declarations and their SPEC-C17 diagnostics, remain in the gate.
The stopped367-root attempt is not reused as evidence of a successful audit.

Focused driver admission55778 was refused at2026-11-08T07:51:53.875240Z:
allowed=false/exit78, bounded51405389824B plus requested8589934592B would exceed
safe59055800320B. Lean did not run; the ID is spent. No source failure, cap
change or bypass. Resume driver2 at a fresh ID after the180s cooldown.

Recorded review at594s:346 fresh root graphs, first partition exit0, cgroup
peak3325083648B, continued new-root progress. No memory or timeout change.
Final exit0 at13:44.47, process peak7036492KiB, swap0; all three partitions
exit0. review-55495-10min.json retains the contemporaneous measurement.
