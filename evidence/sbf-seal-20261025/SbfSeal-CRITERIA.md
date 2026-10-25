# SbfSeal criteria and design (before implementation)

Entry: 50ab99cfbf3febcea66046e017be3e619ca8c732, assigned branch only.
Read /Users/dominic/ZK/AGENTS.md and both supplied common/local rules fully.
Only tools/sbf-seal-20261025 and evidence/sbf-seal-20261025 may change.
All host/network/privilege/compiler/native/key operations have ZERO allocation.
Only small ordinary local Python path/synthetic tests are authorized. No delegation.

## Replacement boundaries

The old SbfClosure_setup.py remains an immutable comparison input; replace its
unsafe implementation in a new SbfSeal module, never patch the shipped/helper
paths. No CLI or approved privileged manifests. Even editing an allowlist must
not bypass the unsupported current GO producer/runtime/kernel gates.

Use a fixed prospective /var/lib/SbfSeal-20261025-v1 exclusively created under
component-opened root-owned, non-group/world-writable /var/lib ancestry. Reject
symlinks and hardlinked files. Ordinary test trees use the caller UID explicitly;
that is not root ancestry validation. All descendants created/opened by dirfd;
all ownership/permission operations by fd. No pathname chmod/chown/copy/mount.
No mutable same-uid host capture root. No source symlinks in the tiny probe;
future finite link graph needs separate reviewed mapping. Verify source metadata
and digest before and after copying; verify destination bytes/inode, seal by fd.
Failure leaves non-executable partial material for review, never deletes keys.

Public stdout/stderr: exact exclusive files under pinned root-owned output dir,
parent retains read fds, child writes only these files, 16KiB each maximum,
collect only after verified child wait/exit and inode/size/rights checks. Fixed
public formats only; no arbitrary root read/export. Guest has only 0,1,2 after
exec; inspection directory fd is closed before checking survivor set. Unknown
FD inventory is denial, no residual fd3 exception. RLIMIT_FSIZE and parent
bound checks are needed; no untested claim of continuous enforcement.

Fresh admission route: outside prospective scan -> new exact 3G/4G/swap0/tasks64
scope -> actual inside scan -> bounded collector/sudo/helper host ancestry and
same-cgroup identities -> kernel setup. Compare actual host PID/starttime, never
guest IDs; permit only explicitly pinned sudo intermediaries, no getppid shortcut.
Compact receipt derives raw report hash/size and selected fields from full exact
ResourceRssGO schema plus pinned producer. Existing marker-only route DOES NOT
authorize a helper. New route, RLIM_INFINITY repair and runtime pins unreviewed:
explicit unsupported denial before any privileged effects. No invented allowed
boolean, TTL, old epoch/unit/GO reuse or changes to 55/7/2GiB policy.

Preserve ordered namespace gates: host admission, unshare mount/net/PID, fork,
verify all changed, private propagation, finite copy/seal/RO view, private proc,
minimal devices, fd chroot, drop bounding/ambient/capabilities/groups/IDs + NNP,
verify, fixed tiny Python exec. Unknown ABI/mount/runtime/GO denies; no host exec.
Implement known ordinary filesystem operations concretely; unsupported Linux
steps must say precisely what review/measurement is missing, not mock success.

## Evidence and completion

Pin immutable old helper, f29c3e0e8c/468-era producer and dependencies, current
SbfResolve receipts/traces and current ELF hashes. Candidate cache mapping is
428 packages, not 123/305 selected necessity; SDK bin/platform-tools-sdk/sbf.
Criterion external target was never entered: omit only if proved unreachable,
otherwise require finite exact release-manifest resolution. No cache-wide binds.
Preserve strict trace subset and name actual trace obstructions. Runtime closure
remains partial. Source packet includes future exact argv, full AST comparison,
manifest hashes, retained failures and test receipt with argv/exit/wall/RSS/swap/
revision/runtime/dependency hashes and axioms N/A. No >5MB derived JSON in Git.

Acceptance: concrete fd path/output/identity/GO rejection code and negative tests,
ordinary nofollow/exclusive/rename/hardlink checks, mock ordered effects, exact
manifest/argv/UID/path denials. Tests distinguish actual ordinary OS operations
from mocked privileged metadata. No Linux privileged result claimed. Both deployed
targets NOT ESTABLISHED. No theorem premise or trust/security contract change.
