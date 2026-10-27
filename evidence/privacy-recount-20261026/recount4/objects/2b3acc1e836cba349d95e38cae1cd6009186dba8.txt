# Missing shared Lean infrastructure

At19:50 UTC the task's path mapper projection finished at its180second cap.
Before the next Lean25401, the scanner admitted8GiB but scp failed with:

```
scp: dest open "/home/dombarker/project-offloads/aspis-joint-20261019/sources/R1Z/PV_Src_CanonicalNormalize.lean": No such file or directory
```

A read-only check found both the full `aspis-joint-20261019` directory and
`r1-privacy-build-integration-20261019/tools/run-joint.sh` missing. No replacement
joint path appeared in the immediate offloads inventory. The task repo,
kani-target, receipt collector and reservation-existing.py remained present.
The lead was asked for replacement/restoration; the task continues independent
Kani verification and statement work.25401 charged zero, not reused.

The local-lean rule5 requires: “Do NOT build or repair build/launcher/monitoring
infrastructure. If the launcher or host misbehaves, stop and report the exact
error in one paragraph; the lead fixes infrastructure. Proof work only.” No
shared cache, launcher or monitor was recreated or edited. Remaining7 Lean
attempts are reserved for proof compiles when an authorized launcher/cache is
available. The cached accepted results already downloaded remain valid for
their exact source/dependency hashes; they are not evidence of a new replay.

Solver-temp hygiene: at19:52 a read-only glob found only
`/tmp/external-sat4011451.IoNxkD.cnf` dated19:18, outside this task's timeout
intervals (full18:36–18:44, values19:28–19:31, path19:47–19:50).
It was not attributed to this task and was retained. No blanket /tmp cleanup.
No wallet key was created, removed or inspected by this task.
