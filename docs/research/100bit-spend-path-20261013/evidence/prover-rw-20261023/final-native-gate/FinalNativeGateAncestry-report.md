# FinalNativeGateAncestry observation

One authorized SSH action was preregistered and spent at 2026-10-25T04:34:30.345181Z, revision 7f59302380f875d4565bd1893e5d573b6530aacf. Exact argv, input/interpreter/SSH hashes and criteria are in plan-v3 and receipt. SSH exit1; wall0.650162s; stdout400B and stderr136B, all inspected. No timeout/disconnect. Axioms N/A.

| Literal path | Type | UID:GID | Mode | Directory | Owner0/1000 | mode&022==0 |
|---|---|---|---|---|---|---|
| / | directory | 0:0 | 0755 | pass | pass | pass |
| /home | directory | 0:0 | 0755 | pass | pass | pass |
| /home/dombarker | directory | 1000:1000 | 0750 | pass | pass | pass |
| /home/dombarker/project-offloads | directory | 1000:1000 | 0775 | pass | pass | FAIL (020) |
| /home/dombarker/project-offloads/codex-cx-prover-rw-20261023 | directory | 1000:1000 | 0775 | pass | pass | FAIL (020) |
| /home/dombarker/project-offloads/codex-cx-prover-rw-20261023/final-native-gate | stat reports ENOENT | unknown | unknown | unknown | unknown | unknown |

First observed failure: `/home/dombarker/project-offloads`, group-write bit020. GID is descriptive, not a check_directory predicate. With current UID1000, these are current metadata evaluations of frozen receiver lines26–28, not invocation of the receiver. The receiver checks each ancestor before leaf mkdir; its additional user-owned parent check would pass the observed assigned-parent UID. No leaf metadata supports assessment of its private0700 requirement. Stat ENOENT concerns this literal path observation only; no target-file conclusions follow.

These are non-atomic path observations, not O_NOFOLLOW FD admission or an immutable whole-chain proof. UID1000 is reused from lead context. Historical DATA failure/status evidence was not rerun or promoted to an identity gate. No configuration change or historical root cause is established; the observed write bits supply a sufficient present rejection condition if seen by check_directory.

Recommended next PATH deliverable for lead review: use a dedicated private parent directly under `/home/dombarker`, for example `/home/dombarker/aspis-private-offloads/codex-cx-prover-rw-20261023/final-native-gate`, outside the group-writable project-offloads ancestry. This is a proposed location, not inspected or created. A separate allocation must prepare/review the path-bearing source/seal changes and parent setup, then establish fresh admission. Preserve nonwrite ancestry, root/current ownership, user-owned transfer parent, no existing-leaf adoption, and all nofollow/FD identity/race checks. No repair or second DATA action executed.

Two local pre-SSH failures are retained: macOS rejected RLIMIT_AS then RLIMIT_RSS before ledger/spawn. Their original scripts, plans and error records remain. The changed v3 capture used alarm40s, SSH deadline20s, output64KiB and sampled aggregate RSS stop512MiB, with no hard-memory-cap claim. Sampled Python+SSH peak27984KiB; Python rusage peak24395776B; children rusage peak4800512B (includes local ps); reported local self/child swap counts0. Remote RSS/swap/tool hashes were not observed; no extra host command was authorized. Early failed invocations have no RSS/swap or exact UTC-time measurement; that missing evidence is explicit.

Only new FinalNativeGateAncestry evidence changed. Frozen receiver SHA25635092a375a438c7ae92cd643d3c9a261f96f7f870b04fc55b17b7a975dd7b0e4 remains unchanged. No shipped source/protocol/wire/features/security-contract changes, trust assumptions, key reads/destruction, heavy scopes, setup or workloads. Lean/Kani/compiler/extraction/native/backend/Rust/Cargo/ELF/root/install actual0. finalKani59/60 reserved and soundness365/368 unchanged. Frozen source boundary, SDK/runtime/extraction, final fresh roles and both security targets remain OPEN/NOT ESTABLISHED. Stop for lead review.
