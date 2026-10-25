# ResourceStability preregistered criteria

Entry 09cf0841c31394f517bc07f1c99eac4e856b8a42, branch
codex/cx-resource-stability-20261025. Only this job's tools/evidence directories
may change. OFFLINE ONLY: no host reads, SSH, scopes, compilers, Rust, Lean,
Kani, extraction, backend, ELF, consumers, keys, RPC or privileged operations.
Python below 512 MiB. Public live API DISABLED; no admission adoption.
Both security targets remain not established; Kani 59/60 final gate reserved.

Before predicate: complete observations, legacy visibility/frontier binding,
phase/scope binding, and ResourceAvailable.membership(before)==membership(after),
then the checked strict numerical predicate. Membership includes every unrelated
PID/TID/starttime as well as topology/controls, but not pids.current.
After predicate (version ResourceStability20261025-v1): independently validate
BOTH complete observations first; require explicit collector PID/starttime/
unified path/path equal and present in validated membership in BOTH phases;
compare an explicit ordered structural/control projection, including root,
parent, owner, controllers/delegation, type/domain, populated, cap/high/swap_max,
tasks_max/pids controls and procs_errno. Only unrelated procs/threads/identities
and internally validated pids.current may differ across snapshots. Retain ALL
raw membership/count differences as diagnostics, not an exception whitelist.
No unknown, vanished, unreadable or malformed identity WITHIN either snapshot
is excused. No row removal, max-current substitution, tolerance or raw scanner
field omission. Inside-scope use unchanged bind_scope plus explicit expected
unit matching. No callbacks or modification of old evaluator globals.

Numerics unchanged: B is full populated finite cap frontier. R=MemTotal-MemFree
-sum(top owner currents); T=KReclaimable-floor(SReclaimable/2). Checked uint64:
Aadj=min(MemAvailable)-max(Active(file))-max(T)-max(R). Strict B+Q<55 GiB,
B+Q+7 GiB<Aadj, min(MemAvailable)>Q+2 GiB. Preserve phase, legacy, caps,
swap, effective ancestors and count-once checks. No physical, future, atomic
reclaim or blanket stronger-domain claim. No protocol/native/security theorem.

Before implementation: assess pinned primary-source references and exact code
dependencies. Implement a small versioned evaluator using pinned unchanged
scanner/observe/bind_scope; explicit source diff for copied evaluator. Focused
new tests only: consistent unrelated exit/birth and numerical noninterference;
collector disappearance/reuse/move; structural/control/ancestor/unit changes;
internal missing/unreadable/malformed IDs and strict arithmetic boundaries.
Original v2 API must consume all 14926 retained events and reconstruct exact
ordered/report hashes and DENY. Apply new policy to the SAME complete captured
pair as counterfactual only. Assess initial 14866 pair as reused inputs; preserve
old scoped-env failure UNKNOWN and DENIED, no historical recertification.
Seal source/dependency/input/interpreter hashes, exact command, exit, wall,
RSS/swap/revision, full axioms N/A. >5 MB derived JSON hash+size only. Retain
failures; stage commits plain, path-limited; no merge/push. Next live work needs
separate review and explicit allocation, regardless of counterfactual outcome.
