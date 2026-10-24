# ResourceAdmit v2 changed-source allocation

Entry 5e59131ea16205a394e3e3a85d4186fe955b3d98. One additional charged
metadata epoch, total at most two. Old epoch and every old capture, manifest,
sentinel, trace and receipt retained. No compiler/formal/native/solver/consumer
execution; private Kani 59/60 final 1 reserved. N/A axioms. Both security targets
not yet established. No merge/push, contract, protocol, trust or frozen-pin change.

Before: systemd-run directly starts pinned Python; parent env=manifest env does
not establish child environment equality. Old differing field UNKNOWN.
After: exact literal /usr/bin/env -i followed by sorted pinned allowlist values
INSIDE scope argv, then /usr/bin/python3 -I -B host.py go. Pin env binary, its
Linux x86-64 loader/libc dependencies, existing language/locale/runtime/tools,
exact argv and epoch/stage/unit. Strict environment equality unchanged; no new
runtime exceptions. Failure diagnostics contain only missing/unexpected key
names and expected-key observed-value digests, never dirty values.

Source/design/focused tests committed before any host operation. New owned
0700 stage /home/dombarker/project-offloads/codex-cx-resource-admit-20261025-v2;
unit resource-admit-20261025-v2; all local captures in this v2 subdirectory.
New local and remote exclusive once-sentinels charge before collection;
transport/observation failure terminal. Existing global flock retained. Manager
coordination update: SbfInputs terminal 0 c3c81cb691 merged 8373ebf51b,
RootExport terminal 0 a554 merged 7b3ff55; Port29 SDKDATA16027 local only;
upcoming SbfClosure waits for this process terminal. No obsolete PID wait.

Fixed unchanged Available policy: one prospective Q=4GiB, full finite B,
B+Q<55GiB, B+Q+7GiB<min M-max active file-max(K-floor(S/2))-max root residual,
min M>Q+2GiB. Strict raw/visibility/PID/control/race/ancestor/frontier gates.
Prospective DENY means no scope. Pass permits only ONE High3G/Max4G/Swap0/
Tasks64 scope with real inside GO Q=0, actual proc identity and effective
controls, then tiny marker only. GO failure means no marker. No size search,
cap raise or retry, even for another cause. Full source/env/runtime pre/go/post
pins, ordered causal replay and peak/swap controls required for actual PASS.

Reuse historical 16 groups, old 14866-event prospective/report hash and DENY
audits, and Available/Actual historical assessments; do not rerun those suites.
New tests target injected INVOCATION_ID/JOURNAL_STREAM/SYSTEMD_EXEC_PID/unknown
keys and value drift, real env reconstruction, strict dirty denial, argv quoting,
v2 binding and exclusive charge identity. New traces alone get complete replay.
All raw originals retained remote; derived >5MB hash/size only, full bounded
ordered shards locally. RSS snapshots distinguished from peak. No root/security/
mount/service/cache/key changes. Any new blocker retained and allocation exhausted.
