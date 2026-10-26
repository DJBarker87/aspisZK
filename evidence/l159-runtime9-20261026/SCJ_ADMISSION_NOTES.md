# Reservation handling

Every attempt invoked the existing host reservation.py with stdout/stderr
redirected to the host SCJ_NNN-barrier.log BEFORE copying any source/config.
Only one capped scope ran at a time for this job. The original launchers and
reservation script were not modified.

SCJ_023's first reservation scan hit a vanished cgroup belonging to another
job (our preceding SCJ_022 scope was run-rcc8bb6d609754be5a7c8f7075a4a7ee6).
The diagnostic observed before retry was:

```
FileNotFoundError: [Errno 2] No such file or directory: '/sys/fs/cgroup/user.slice/user-1000.slice/user@1000.service/app.slice/run-r1a2ad77b3676479eb5ebebeeefe4c0fa.scope/cgroup.procs'
```

No reservation JSON existed. The unchanged task orchestration waited 30 s
and retried the reservation step once, as local-lean rules 6-7 require.
SCJ_023-retries.json records that wait; the final barrier log/JSON record
admission. The prefix-only inherited orchestrator overwrites its barrier log
on each retry; this note preserves the initial observed failure. No Lean
compile was launched for the failed scan, and no barrier/cap was bypassed.
