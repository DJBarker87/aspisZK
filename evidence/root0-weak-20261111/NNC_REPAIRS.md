Own prelaunch share-check at L038 failed before admission/launch: reading one running scope's cgroup.procs returned errno95 (Operation not supported). Linux threaded cgroups expose task IDs through cgroup.threads instead. Own NNC_transport.py now falls back ONLY on errno95 to reading the SAME cgroup's cgroup.threads; every thread's cwd is inspected by the same rule. No cgroup is skipped, fallback failure still stops, all six-scope/admission/disk rules remain. No shared script, scope or host state changed. The failed transport stderr is retained in NNC_TRANSPORT.jsonl; no compiler scope was consumed. L038 reuses only the unsubmitted attempt identifier.

Option B import inspection: L060 read public module headers only and missed
private imports. L061's owned inspector incorrectly skipped the `.server` part
before loading `.private`, causing exit139 (not a proof or host failure).
L063 uses the exact main/server/private order from Lean.Environment's loader.
No shared launcher, shim or cache was changed.

Option B final audit orchestration: the owned formal runner now emits C for
NNC_OptionBDriver as well as the old audit drivers. NNC_batch selects that
new driver ONLY for appended groups8+, retaining the original groups0-7 and
their successful receipts. The manifest appends72 new own roots; no unchanged
root audit or full regression is repeated. Validation compares own changes
against cfa73190568 (the lead's inherited research/amendment merge), because
comparing against the older job base incorrectly attributed merged lead work
to this continuation. The same strict only-own-evidence and capped-admission
checks remain. No shared infrastructure was changed.

The intermediate NNC_ProbabilityFold.averaging_step (L075) is RETIRED from the
active/exported interface: it took nativeInclusion as an OPEN fold parameter.
The stronger NNC_RecordedEnvelope.bound (L094) instead bounds the joint
runtime/E_rec envelope with NO inclusion premise, by using the SAME event
indicator on both sides. The old source/receipts remain as .lean.retired;
no final native theorem is obtained by assuming inclusion. The audit manifest
excludes that retired root; all other new roots are checked once.
