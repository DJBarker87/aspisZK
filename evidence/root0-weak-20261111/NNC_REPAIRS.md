Own prelaunch share-check at L038 failed before admission/launch: reading one running scope's cgroup.procs returned errno95 (Operation not supported). Linux threaded cgroups expose task IDs through cgroup.threads instead. Own NNC_transport.py now falls back ONLY on errno95 to reading the SAME cgroup's cgroup.threads; every thread's cwd is inspected by the same rule. No cgroup is skipped, fallback failure still stops, all six-scope/admission/disk rules remain. No shared script, scope or host state changed. The failed transport stderr is retained in NNC_TRANSPORT.jsonl; no compiler scope was consumed. L038 reuses only the unsubmitted attempt identifier.

Option B import inspection: L060 read public module headers only and missed
private imports. L061's owned inspector incorrectly skipped the `.server` part
before loading `.private`, causing exit139 (not a proof or host failure).
L063 uses the exact main/server/private order from Lean.Environment's loader.
No shared launcher, shim or cache was changed.
