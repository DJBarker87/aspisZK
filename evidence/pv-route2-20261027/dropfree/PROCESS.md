# Invocation and admission notes

All measurements use the unchanged pinned extractor with preflight on. No local Lean compilation. The fresh budget is separate from the historical 52100-series budget.

The first two admission scans encountered vanished unrelated cgroups (charon-252-01 and aeneas-252-02); each refused scan started no scope. They were followed by fresh receipt names after the required 30-second wait. Aeneas-252-03 consumed the already generated LLBC, avoiding an unchanged Charon rerun. Its loop version passed preflight but failed internally. The next source expands the known fixed loops; it is a changed input, not an unchanged failed rerun.

53300–53302 are admission-only IDs. The aggregate gate reported 51,405,389,824 reserved bytes and 59,995,324,416 projected bytes against a 59,055,800,320-byte safe limit. No Lean compile was charged. 53302 was requested less than three minutes after 53301: this was a retry-cadence deviation; admission still refused and no scope started. The subsequent invocation wrapper waits the full three minutes and advances to the next unused ID after every refusal. Shared reservation/launcher files were not modified.

The per-job invocation wrapper records transient scanner errors and wait/retry actions; it does not bypass the gate or increase caps. Each scope has MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64. The accepted shared Lean launcher setting remains TasksMax=128. Only one scope in this job is allowed at a time.
