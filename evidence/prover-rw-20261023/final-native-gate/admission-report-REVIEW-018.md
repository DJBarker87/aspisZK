FinalNativeGate admission report — SOURCE ONLY; STOP FOR LEAD REVIEW

Branch: codex/cx-prover-rw-20261023. Base ee8335334c299ef379fe23785740137d6bc4082d.
Source stage: f5f253b4c4. Both security targets NOT ESTABLISHED. The actual
prospective decision/reason remains UNKNOWN. Maintained setup is UNSEALED;
NO RELEASE ALLOWED. No formal assumption was discharged, added or changed.
No theorem statement/premise, shipped source, protocol, wire, feature, security
contract, publication implementation, historical 011/action/actualv4/v4 release,
key, or other worktree was changed. No merge or push. Port36/PID1483 untouched.

Concrete source progress

The maintained collect('prospective') calls save('prospective-report.json',report)
after adding raw_receipts=[ordered]; later report/metrics receipts are added to
the returned object only after this report is saved. The adapter returns decision,
snapshots, original_legacy and collector metadata. The embedded policy evaluate
puts legacy visibility INSIDE decision; collection_failures can contain raw_inputs
and read_attempts. These hidden structures were inspected as source data, never
imported/executed. Complete observation/adapter functions and policy evaluate are
in admission-report-functions-018.json, with exact source pins. The new reader
is a concrete modification of the frozen reader, not a wrapper or policy fix.

New tools under tools/prover-rw-20261023/final-native-gate:
- FinalNativeGate-admission-report.py: disabled main; exact prospective report.
- FinalNativeGate-admission-report-payload.txt: same source with only terminal
  main() call replaced by diagnostic_entry().
- FinalNativeGate-admission-report-transport.py: disabled main, future body only.
- FinalNativeGate-admission-report-tests.py, -check.py, -audit.py: local fixtures,
  sampled resource watchdog and source review, no host actions.

Full function BEFORE/AFTER, unchanged functions included, are in
admission-report-functions-018.json. Complete reader/transport/checker source
diffs are in admission-report-source-diff-018.txt. New literal namespace leaves
the old payload, old capture and already-spent transport unchanged. Comparison
is against immutable base Git bytes. Import catalog, exact source/payload/transport
seals, local loaded dependency hashes, reuse assessment and future command are
in admission-report-seals-018.json. Formal before/after statements: N/A.

Reader contract

Reads ONLY /home/dombarker/final-native-gate/FinalNativeGate-setup-packet/prospective-report.json
and literal ancestor metadata /, /home, /home/dombarker, stage, packet. No glob,
log, process/proc, environment, cache, secret, config, systemctl, key, source-content
import, content exec or other file read. Root/current-owner nonwrite directories;
home current UID; stage/packet exactly0700. Relative O_NOFOLLOW entry/fd opens;
full stamp dev/ino/mode/UID/GID/nlink/size/mtime/ctime, excluding atime, checked
across the interval. File regular/currentUID/nlink1/no world-write, alias checks.
Whole-interval drift removes hashes/content; all opened descriptors close, at
most six. Timeout now escapes the row OSError handler and denies the interval.

Original predicate BEFORE = AFTER:
  regular AND nlink=1 AND owner=currentUID AND (mode & 0o022)=0.
Group-write-only debug reading remains a separate explicit exception, recording
original failure. Every value remains UNTRUSTED DiagnosticBytes even on stable
intervals. No approval, identity, canonicality, GO, execution authority, release,
formal implication or cancellation/closure follows. Stable means sampled entry/fd
interval only, never writer absence or a historical source identity.

At most2MiB actual file bytes and total bytes. Successful bounded reads stream
hash the COMPLETE exact file; strict whole-file UTF8/JSON, duplicate-key,
nonfinite/overflow/numeric parse errors retained; top-level dict required.
Selected keys only: decision, collection_failures, phase, error/errors,
reason/reasons, schema. Decision is projected to explicit semantic keys; failure
labels visibility/before/after retain error/type/errno/reason/reasons. Nested raw
visibility, legacy, snapshots, raw receipts/inputs/attempts, ordered inputs and
environment objects are omitted. Complete original selected-field canonical JSON
hash/size are retained BEFORE projection (sorted keys, ASCII, compact separators;
these field hashes are not hashes of original lexical byte slices). Selected
output, INCLUDING hash/size/keys/omission records, <=64KiB combined. Oversized
selected values have explicit truncation_error and omitted content, no prefix.

Explicit unresolved requirement conflict: an oversized report cannot both have
its complete SHA256 computed and remain within a2MiB read cap. This proposal
preserves the strict cap: stat metadata + bounds denial + hash_unavailable,
ZERO content reads/parse/fetch for size>2MiB; no fabricated or partial hash.
A complete oversized-file hash is NOT established. No stream parser, cap raise
or expanded query is proposed. Lead review must retain this limitation before
any later allocation; this worker asks no owner question and runs no query.

Transport review (NOT invoked)

Payload:10257 bytes SHA256 da8b1f52c34a012399c1fab602b12b31c3826f31f3544ef6df48827d25c3f290.
Transport:7269 bytes SHA256 8cbdaa628f3cce076814fcf9b3be33c77bac403a8730fb67e4ce1354a8839258.
Fixed fresh capture, checked ABSENT by fixtures and audit, never created here:
/private/tmp/FinalNativeGate-admission-report-012-future
Exclusive0700 capture/0600 files and durable exclusive charge before any future
Popen. Exact payload fd as stdin. No retry/adoption/overwrite of spent captures.
Remote alarm10s, max6FD; local20s, combined4MiB, sampled self+SSH512MiB;
no RLIMIT_AS/DATA/RSS setters. Sampled RSS is not a continuous-memory theorem.

Exact future SSH argv, NOT RUN:
/usr/bin/ssh -T -oBatchMode=yes -oConnectTimeout=10 -oStrictHostKeyChecking=yes -oClearAllForwardings=yes -oForwardAgent=no dombarker@100.108.41.90 '/usr/bin/python3 -I -B -'

Exact future local invocation, NOT RUN; later explicit lead authorization only:
python3 -I -B -c "import runpy; m=runpy.run_path('/Users/dominic/ZK/.worktrees/cx-prover-rw/tools/prover-rw-20261023/final-native-gate/FinalNativeGate-admission-report-transport.py',run_name='reviewed_source'); raise SystemExit(m['_reviewed_future']())"

New validation and preserved failure

Exact per-run argv, revision, all source/dependency pins, interpreter hash,
exit/wall/self+child peak/sample RSS/swap and full axioms=N/A are recorded in
admission-report-tests-012 through017 and admission-report-audit-018 JSON/logs.
These are Python source/fixture results, no formal import/axioms theorem.
Tests ran on base ee8335334c plus hashed working sources; final017 reader,
payload, transport, fixture/check bytes equal source-stage f5f253b4c4. The audit
ran at f5f253b4c4. Neither is a new remote artifact identity gate.

Exact final fixture command:
python3 -B tools/prover-rw-20261023/final-native-gate/FinalNativeGate-admission-report-check.py admission-report-tests-017 FinalNativeGate-admission-report-tests.py
14 cases PASS; exit0, wall0.19507833430543542s, self peak21282816B,
child peak42270720B, sampled self+child53280768B, swap0.
New fixtures include concrete nested legacy/failure redaction, denial reasons,
group-write original failure, exact2MiB full hash, oversized no parse/read,
combined nested field bounds, duplicate/nonfinite/invalid UTF8/numeric errors,
FD/entry/owner/alias/partial/missing/read-error/alarm paths, closure, payload pin,
argv, disabled main, absent capture and durable-charge exclusive mock transport.
Fresh private fixture roots are retained and final017 prints exact locations.
Mock SSH_charged=1 is synthetic; actual SSH count remains ZERO.

Exact audit command:
python3 -B tools/prover-rw-20261023/final-native-gate/FinalNativeGate-admission-report-check.py admission-report-audit-018 FinalNativeGate-admission-report-audit.py
PASS; exit0, wall0.9586974158883095s, self peak21790720B,
child peak102465536B, sampled self+child47579136B, swap0.
All source jobs <512MiB and30s. No uncapped build or host reservation launched.

012 PASS initial9 cases;013 FAIL alarm fixture exposed TimeoutError being caught
as row OSError, leaving interval_stable true. Failed source AND test snapshots
retained as admission-report-failed-013-*.txt alongside original receipt/log.
Replacement rethrows timeout to whole-interval handler;014 PASS11 cases.
015 PASS12 adds concrete nested legacy/failure projection;016 PASS13 adds nested
raw exclusion and new transport mock;017 PASS14 adds exact2MiB boundary and
explicit retained fixture locations. No unchanged failure or regression rerun.

Reused validation, explicitly historical

Publication011 receipt and exact current maintained publication source/test pins
match; no publication change or repeat. Transport010 test source matches; its
whole transport pin differs because later diagnostic payload literals changed.
Audit proves its pinned80c7917238 blob's COMPLETE _reviewed_future function equals
both the frozen current body and new body. Unchanged boundary mocks are reused
only for that body; new literals get final017 focused mocks. Diagnostic011
source assessment also records exact current transport/test pin match. None
provides a new host identity or full-release gate. Historical reader exit0,
stable interval, all three0664/original mode022 failures and terminal admission/
scope-unbound errors are reused from the complete ReceiptAction report. Actual
underlying decision still UNKNOWN. unresolved=false is DATA, never closure.

Unchanged state and next deliverable

setup_observe.save remains ambient-umask hash-only legacy telemetry. No claim
that this report was privately published;0664 does not uniquely identify umask.
The0600 publication repair from8f remains accepted SOURCE only, unsealed.
No scope-bound source fix, admission retry, v5, new stage, action, release seal
refresh, native/Kani/Lean/compiler/ELF work or full frozen manifest occurred.
Actual SSH/host/root/sudo/namespace/setup/probe/native/compiler/Lean/Kani/ELF
counters ALL0. No process/role query was appended. Keys retained untouched.

All trust and formal boundaries remain: Python/stdlib/SSH/OS operations and all
SDK/std/runtime/allocator/extraction/child/mark/P2Prime/native joins. No output
or adaptive-oracle/event-law equivalence claim. Binding security contract and
current ELF pins unchanged: default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4,
devnet63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299,
Pool121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548.
Budgets unchanged: Kani59/60 final reserved; privateLean240/260;
extraction54/56; backend15/16; Rust2/3 actual ordinary1; ELF0/3;
soundness366/368 with367/368 reserved. No derived JSON>5MB committed.

Next deliverable belongs to lead review: assess the new fixed source/payload/
transport, semantic projection and explicit oversized-hash limitation; only a
later separately authorized read-only query could reveal the actual reason.
Both security targets NOT ESTABLISHED. STOP FOR LEAD REVIEW; NO ACTUAL QUERY.

Packaging note: source-only git diff --check passed. The staged evidence
whitespace check reported15 blank context lines in admission-report-source-diff-018.txt
(the literal space prefix required by a unified diff). The complete diff is
retained byte-for-byte; these are patch context, not trailing spaces in source.
No source or fixture changed after the passing017/018 results.
