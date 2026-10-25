# Source-only review handoff

Candidate: exact immutable 9fe9f199d1e52e3dcf4b355dff57330e5019a220 snapshot source, except original `scan` renamed `scan_once` and one bounded `scan` wrapper. Byte-for-byte renamed function and complete remaining AST equality passed. `tests.json` contains full source pins, wrapper SOURCE/function SHA256, wall/RSS/swap/exit and axioms N/A. Candidate SHA256: 30895796730e70da8f36e9d832d93e7dc2633fc73f860c9b394b90a2a9ec4028 (19388 bytes).

Four total fresh attempts maximum, only errno 2/3 on canonical positive ASCII decimal TID stat/status/cgroup paths. No sleep, skipped PID, partial acceptance, memory credit or zero-growth claim. Successful receipts remain exclusively from the successful scan. Compact discarded provenance is separate. Retry errors lose raw annotations and traceback scan frames; fourth failure propagates with all four compact failures. Complete original validation remains mandatory.

Seven focused tests and sixteen reused generic tests passed. Focused scans are fakes. Two original generic parser/error tests invoke the original scan only with mocked `Path.read_text`; no live procfs/sysfs read occurred. This is narrower than live collection but does invoke the original parser under mocks. No compiler ran. Test wall 0.147s, RSS 35225600 bytes, swaps 0, exit 0; below 512 MiB. No artifact exceeds 5 MB.

Next: lead review and pin adoption into existing profiles/privacy bundle only; no execution grant. Profile patching MUST retain the original scan under `scan_once` in the wrapper globals (`needs_scan_once_original_alias=true`), then bind wrapper `scan`. Preserve ResourceStat_go scan_bound source binding: unchanged self-before, base['scan'](), self-after; both outer before/after collections keep that bracket. Source pin and function hash are in tests.json. No profiles were edited.

Both security targets NOT ESTABLISHED. All source/native/SDK/std/runtime/extraction/allocator/artifact boundaries retained. Quotas, complete identities/scope, dual before/after, structural stability, memory formula and operational rule 63 unchanged. Ordinary bounded metadata refresh proves no atomic state, safety, termination or cryptography. All old failed epochs/scopes/actions remain excluded from new GO. Port actual 368; 369/370 independently allocated/unspent; compiler budget 0; privacy final Kani 59/60 reserved, unchanged.

Exact materialization/test commands:

```
python3 -B tools/resource-capture-retry-20261025/ResourceCaptureRetry_prepare.py
python3 -B tools/resource-capture-retry-20261025/ResourceCaptureRetry_tests.py
```

Scope note: one accidental Git tree-name listing used `tools` at immutable 5756082d; no contents from that listing were read. All subsequent source reads were exact immutable paths. Pre-existing deleted AGENTS.md was read from HEAD and left unchanged; user wallet retention instructions also apply. No host/SSH/live query, cache/raw capture, compiler, key/RPC, push or subagent action.
