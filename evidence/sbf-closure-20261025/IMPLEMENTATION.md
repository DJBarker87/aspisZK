# SbfClosure concrete preparation boundaries

The literal setup backend is a review draft, not an executable sandbox or a
completed build helper. APPROVED_MANIFEST_SHA256 is empty, CLI always refuses,
and Linux.host_gate explicitly denies pending ResourceAdmit-v2 GO schema/freshness
integration. No arbitrary producer-supplied success boolean is accepted. The
only inner argv is a tiny Python assertion probe, never a build command.
Manager review must resolve the listed issues before approving any probe.

The ordered implementation unshares mount/net/PID, forks for PID namespace,
checks all three identities changed, then makes propagation private. Public
files are copied with per-component O_NOFOLLOW and pinned fd pre/post metadata
and content comparison into a new root-owned rootfs. This avoids claiming that
an RO bind stops same-uid host writers. Rootfs receives an RO self bind; explicit
new probe outputs are RW. It mounts descendant proc, three exact devices, enters
by rootfs dirfd, clears supplementary/bounding/ambient/permitted/effective/
inheritable capabilities, saved IDs and sets NNP. Child checks process status.
No host-global cleanup or umount is implemented. Retain failed roots for review.

Unresolved literal implementation review issues (not hidden assumptions):
* GO producer schema/freshness/reservation/parent identity integration remains a
 hard stop. ResourceAdmit released DENY, not a usable GO.
* Probe stdout/stderr are root-created0600 files; user receipt collection requires
 reviewed post-exit handling. No permission/ownership mutation ran this phase.
* Per-file source open prohibits symlink ancestors; input sources must first be
 associated with reviewed resolved public paths. SDK/tool links need reconstruction.
* Root directory construction presently uses path operations after rootfd capture;
 own0700 ancestors and root ownership are intended exclusions but rename/mountpoint
 identity/submount and races require a stronger anchored-dirfd review before use.
* Device mount flags, mountinfo checks, ambient/bounding availability, inherited
 FDs (including stdio) and actual capdrop ordering are unprobed Linux mechanisms.
 Current cap assertion allows transient /proc listing FD3; no claim all privileged
 FDs are excluded in actual execution. Child initial environment uses execve exact
 allowlist; bootstrap interpreter/loader and already-loaded Python modules still
 need a concrete sealed runtime and inherited-state assessment.
* Probe writable mappings are only /tmp and .probe-work. A build would need a new
 exact command/output mapping review preserving all original S10 logical paths,
 not a broadened /home mount. No old target/OUT_DIR enters the probe.

Synthetic39 checks prove orchestrator denial/order and a bounded raw strace subset;
they do not validate real ownership/mount/capability syscalls. No privileged setup
probe, unprivileged namespace retry or root child ran. More source-level fixtures
are needed for the literal backend. This is a concrete draft with explicit stops,
not deliverable2 complete or a generic wrapper promoted to execution closure.

Trace parser consumes exact `PID timestamp syscall(args) = result` lines with
JSON-compatible C strings. It tracks fork, copied fd/cwd state, exec CLOEXEC,
open/close/dup, cwd/dirfd, lexical symlink resolution and exact successful/failed
input joins. Direct build-script exec is included. Unsupported wait/shared-clone/
unfinished/resumed/truncated/unknown syntax fails. Current successful readlink
through a sealed final symlink also rejects conservatively because path joining
follows final links; there is no accepted claim of full readlink support. Failed
unsealed probes fail; no absence certificate producer exists. Strict observed
path subset is not a complete Cargo trace validator, immutable-seal producer,
output/fingerprint cache join, TOU guard or syscall memory/effect proof.

Future trace capture needs close/dup/dup2/dup3/fcntl/fchdir in addition to
%file,%process. No read/write buffers/environment are captured. No actual strace
capture ran. New output identities, OUT_DIR, Cargo fingerprints and cache validity
must be tied to actual executed commands and frozen input seals before reuse;
these remain pending. Initial default cold; devnet only its new validated cache;
Pool distinct new target, no forged fingerprint/mtime or historical compiled input.

Source/release premises: before=after, all theorem/security statements unchanged.
No new trust assumption. Filesystem isolation and postvalidation are engineering
obligations still open, not new cryptographic axioms. Both security targets NOT
YET ESTABLISHED. Full source/model/native/Std/P7/extraction/effect joins stay open.
