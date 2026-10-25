# SbfLinux source-only handoff

Branch: codex/cx-sbf-linux-20261025. Entry:
9f48e742a9df7e628e54aaed4cafead19c4e2537. Final implementation revision:
83517306fa76bc2ad7b55c46c238020d9006d546. Later evidence-only commit does not
change tested Python bytes. No merge/push, shipped source, protocol, model,
security contract, parameters, ELF, keys, or other worktrees changed.

## Exact established source claim

Concrete unexecuted backend exists in SbfLinux_abi.py and SbfLinux_backend.py
(184 + 543 implementation lines, plus two-line disabled CLI; copied primitives
and validation tools/tests separate). The kernel ABI derives from exact Linux
v6.8 commit e8f897f4afef0031fe618a8e94127a0934896aba. Fourteen pinned primary
reference bodies/hashes include syscalls.h, x86 syscall table, UAPI mount/stat/
capability/prctl/sched/fcntl/resource/signal and proc/mount implementation, plus
Python fork documentation. Kernel URLs in references.json are canonicalized to
the resolved commit; original fetch used its v6.8 tag and the tag's commit JSON
is retained. No official documentation is runtime validation.

Source composition: parameterless fixed body -> fixed SbfSeal ancestry/layout,
root-owned public-output and verified readonly null -> root helper preflight ->
unshare MNT/NET/PID -> gated CPython fork -> parent-owned pidfd_open/identity/
signal check -> guest PID1/actual namespace checks -> private propagation ->
fixed ancestry recheck and finite SbfSeal copy/seal/close -> descriptor readonly
clone/attach -> retained NEW mount root -> finite 1MiB/64-inode tmpfs and private
readonly proc -> exact stdio -> descriptor-root chroot -> close_range(3,UINT_MAX)
-> guest-only NOFILE/FSIZE caps without increasing limits -> groups/ambient/
bounding/saved GID+UID/capset/NNP drop -> actual metadata rechecks -> fixed probe
exec. Parent collects fixed bounded public output only following actual own-child
zero exit. Timeout code signals only retained own pidfd and reaps before export;
no numeric PID signal or fallback exec. /dev is empty; root stays NODEV and null
is inherited, with no device binds. Kernel/CPython behavior remains unvalidated.

The exact copied SbfSeal_setup bytes have SHA256
5b4f0f65abd1f3e7548a1c93bb8a8b027dd2b7346588f6f06b203cd2a2e19664.
No fixes to that copy. Historical lead-reviewed 32 ordinary/mock cases and 895
package checks are reused only for unchanged primitives, not rerun or promoted
to a new identity gate. Old unprivileged uid_map EPERM remains historical and
was not retried; no user namespace was added.

## Final new validation

* `PYTHONDONTWRITEBYTECODE=1 python3 tools/sbf-linux-20261025/SbfLinux_check.py v5 83517306fa76bc2ad7b55c46c238020d9006d546`
  — 54 distinct tests PASS, exit 0; in-process wall 0.028943625278770924s,
  peak RSS 34619392 bytes, swaps 0, axioms N/A. Exact interpreter argv, hashes of
  every source and loaded Python source dependency are in tests-v5.json; full
  output in tests-v5.log. Harness forbids real C loads, fork/exec/chroot,
  credentials and limit changes. Mock C reads only its own ctypes buffers.
* `PYTHONDONTWRITEBYTECODE=1 python3 tools/sbf-linux-20261025/SbfLinux_audit.py 83517306fa76bc2ad7b55c46c238020d9006d546`
  — exit 0; wall 0.026237457990646362s, RSS 25821184 bytes, swaps 0,
  axioms N/A. source-audit-v4.json pins all source/reference bytes, public
  function/class names and imports, AST unconditional denials, exact-copy hash,
  package-v4.json and synthetic future-command-v4.json. These are local source
  checks, not a full frozen release manifest or host identity gate.

All local jobs stayed below 512MiB. Actual host/SSH, namespace/mount/root,
Linux backend/native probe, scope/GO, compiler/Lean/Rust/Cargo/Kani, wallet/RPC
budgets used: ZERO. Only official primary HTTPS research and ordinary pure/mock
Python ran. No populated host reservation query was attempted; no host launch
was permitted. All JSON files are below 5MB. Failure bodies, counterexamples,
mock fixture failure, malformed runner argument, and superseded validation are
retained in FAILURES.md and versioned snapshots/logs. The tests-v1 abbreviated
revision 0a6996ecdd denotes full 0a6996ecdd671df74f61e84227c31cf95db309a1.

## Before/after predicates and unchanged obligations

No theorem premises changed and no theorem/axiom audit ran (N/A).
Reused manifest predicate before: version SbfSeal-tiny-v1, argv PROBE, exact
root/uid/gid/env/finite pinned-file schema. New predicate after: version
SbfLinux-tiny-v1, argv FIXED_PROBE with added fixed postexec checks; convert only
version/argv to reuse original schema validation. Root, IDs, environment, finite
file bounds and hash/mode predicates are retained. New restrictions reserve
/tmp, /proc, /dev for setup. This is a concrete source predicate change, not a
proof of runtime completeness or output equivalence. No claimed conclusion is
hidden in a premise; no new trust assumption discharges any security boundary.

RUNTIME_APPROVAL and PRODUCER_ASSEMBLY remain null. Both privileged entrypoints
and the pinned CLI unconditionally deny; changing runtime metadata alone does
not activate CLI. No old marker receipt/admission.project/epoch/TTL is GO.
Future external route still requires current fresh prospective host admission,
new exact 3G/4G/swap0/Tasks64 scope, fresh inside-Q0 count-once actual collector
GO, full raw report/pins, actual collector/sudo/monitor/helper ancestry/control
and all 55/7/2GiB checks. No producer continuation is invented or adopted here.

Next deliverables: independent source review; complete finite tiny-Python
loader/import/resource/proc/stdio/setup runtime manifest; independently reviewed
current producer continuation; separately authorized finite actual Linux 6.8
ABI/mount/FD/capability/cancellation/postexec probe. In particular signal-0 success
does not prove LSM acceptance of SIGKILL; no bounded D-state wait, parent-death,
native-memory effect, owner or runtime security closure is claimed. Actual
runtime gates must resolve those before enabling any privileged entrypoint.
The SDK criterion remains unentered; tiny probe is only an enabler, not Cargo,
ELF or runtime closure. Both deployed targets remain NOT ESTABLISHED.

Current ELF pins are retained as task context only, with no new identity gate:
default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4;
devnet 63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299;
Pool 121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548.
