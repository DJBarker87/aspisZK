# Required infrastructure stop

No Kani scope for K033 was launched. G033 (cargo metadata --locked --offline)
was admitted and exited0, but its combined stdout/stderr begins with:

```
    Blocking waiting for file lock on package cache
    Blocking waiting for file lock on package cache
```

The JSON follows those lines. The inherited LPf_run.py graph gate calls
`json.loads` on the complete stdout.log and raised:
`json.decoder.JSONDecodeError: Expecting value: line 1 column 5 (char 4)`.
Exact command, frozen source/lock hashes, resource metrics and raw output are in
LPf_G033/receipt.json, stdout.log and time.log. The invocation traceback is
retained in LPf_G033-validator-failure.txt. No graph-pass receipt or Kani launch
was fabricated; the parser was not repaired and the job was not relaunched.

local-lean.txt rule5: "Do NOT build or repair build/launcher/monitoring
infrastructure. If the launcher or host misbehaves, stop and report the exact
error in one paragraph; the lead fixes infrastructure. Proof work only."
This is that required stop, before budget exhaustion:28/30 actual Kani
invocations and28/60 Lean compiles. G001–003 and cancelled G021, plus failed
pre-Kani graph gate G033, are not counted as solver invocations.

All proof work stops here. Remaining operations are receipt/source auditing,
own-cache cleanup and the explicitly requested local handoff commit. The lead's
next infrastructure deliverable is a validated way to preserve Cargo diagnostics
separately from the metadata JSON; this worker implements no such change.
After the lead fixes it, powers7_canonical remains an UNRUN safety-only draft,
and every other open native gate retains its exact status in LPf_LEAVES.md.
