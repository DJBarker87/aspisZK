# Required host stop

Attempt 37334 was submitted after the changed generator passed as 37333.
Its wrapper's recorded launcher result is SSH failure; both the collected
`out-37334.log` and `time-37334.log` contain the exact diagnostic:

```
Connection closed by 100.108.41.90 port 22
```

The local receipt has `exit: null`, `peak_rss_bytes: null`, `swaps: null`,
`accepted: false`. The compiler's actual outcome is **unknown**, not a proved
failure or success. The 37.515 s wrapper wall time is not a valid measured
compiler wall time. Do not reuse 37334 or claim that it passed. Recover the
remote output/time/object metadata after the lead restores host operation.
No new scope is started after this error.

Governing instruction: `local-lean.txt` rule 5, read through pv-common:
"Do NOT build or repair build/launcher/monitoring infrastructure. If the
launcher or host misbehaves, stop and report the exact error in one paragraph;
the lead fixes infrastructure. Proof work only."

This is an infrastructure stop, not a reservation refusal, budget exhaustion,
a failed-lemma stop, or a checked native counterexample. The failed lemmas and
the isolated memory failure were retained and work continued after them.
35 IDs consumed (37300–37334): 34 known scoped receipts, 1 unknown compiler
outcome; conservatively reserve all 35 attempts. 65 attempts/IDs remain,
including unused audits 37397–37399. Zero Kani. The pinned private cache and
sources are preserved for continuation; no keys were touched.

The wrapper for 37334 was started before 37333's final receipt retrieval
finished. 37333 had exited its scope and was collecting time metadata; no
second live capped compile scope is evidenced. Future queue/resume work must
await the entire preceding wrapper, not just its LAUNCH line, before invoking
the next wrapper. No launcher/admission/cap implementation is changed.
