# Finite probe split proposed for lead review only

No producer source, pin, activation patch, approval gate or deployment policy
changed. No installation, native/backend call or probe exists from this job.

The exact blocking current interface is immutable Producer20a0f5bb38
`SbfProducer_package.approval()`: RUNTIME_PIN must be an exact hash/size dict;
the existing empty tuple fails `published reviewed runtime closure unavailable`
before any native call. Both `user_producer()` and `root_continuation()` in
`SbfProducer_continue.py` call approval before their effects. The latter then
requires root-owned PACKAGE/runtime files. `producer_fixed_body()` rereads
approval; `fixed_backend_body()` separately requires RUNTIME_APPROVAL to be a
dict, currently None. Installed user/root entries unconditionally deny.
`DEPLOYMENT-REVIEW.md`, “Missing publication, not a permission request”, requires
exact source/runtime closure including stdlib/extensions/loaders/sudo/monitor/
plugins/config/ps/systemctl/docker, roles, controls, scope and signatures.
Thus the current producer cannot be used as a bootstrap validation probe while
that complete-runtime publication remains missing. No evidence here supplies it.

Proposed source-only split (NOT implemented or approved): prepare a distinct,
fixed finite-validation-probe integration artifact for lead review. It should
pin the exact finishing payload and input plan, then later pin the resulting
finite candidate bytes and complete alias-chain mapping, publish the exact
fixed backend/postexec probe source, explicitly reconcile SbfLinux-tiny-v1's
old root/argv/names with any Producer-specific root/argv/names, and specify fresh
root-only exclusive-copy installation. Current candidate-template data uses
SbfLinux schema; it is NOT an accepted SbfProducer runtime manifest. Never
silently rename, substitute the Producer argv, reuse a signature, or claim a
new release identity. The artifact needs independent probe-specific fixed
admission/role/scope/descriptor/lifecycle controls and an explicit bounded
allocation before any execution; it must retain capture and failures.

Such a probe answers whether this exact finite INPUT DATA supports that exact
bounded private-rootfs experiment. Its result cannot authorize production,
activate current producer entries, sign complete runtime approval, establish
runtime effect equivalence, or replace the full adoption/security obligations.
The unchanged adoption gate still requires full native/host runtime closure,
real roles/sudo/monitor/plugins/full tools, and OS/kernel/SDK/std/runtime/
allocator/extraction boundaries. Source effects, conditional dlopen, locale/NSS,
private guest/control, LSM, cancellation, parent death and open-FD/inode binding
remain OPEN even if the finite probe later exits zero. Full cryptographic/
adaptive-oracle/event-law joins and both deployed targets remain unestablished.

Before/after claims: no theorem premise changes. Before, the old walker granted
SSL config redirects only when original == /etc/ssl/openssl.cnf, and admitted
subtrees /usr/lib/ssl and /etc/ssl. After, the NEW prospective helper admits
redirects from either exact spelling ONLY to the exact two-file set. Public
paths cannot redirect into /etc. The localtime zoneinfo rule remains distinct;
loader prefixes may be intermediate but not final public roots. Additional
stricter checks are explicit: uid AND gid0, single-link symlinks, fixed loader
config endpoints, held directory FDs and post-read chain/entry checks. No
shipped reader or security assumption was weakened or changed.
