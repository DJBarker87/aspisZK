# SbfInputs filesystem feasibility and exact remaining setup

Status: blocked future proposal. No mount, chroot, privileged namespace, compiler
or scope has run. `finish.stdout.json` retains the literal unprivileged probe:
`unshare --user --map-current-user --mount --net --pid --fork -- python3 ...`.
It exited1 at uid_map with EPERM. This is no diagnosis of host security settings,
ports, Docker state, or a missing kernel feature. Do not retry by changing those
settings. bwrap is absent; installation is not proposed. Narrow read-only sudo
process-metadata permission is not permission to mount/chroot.

## Future setup for separate review

The minimum alternative is a trusted parent setting up one private mount/network/
PID namespace, then dropping the build child to uid/gid1000. The outer parent
must itself already be in the separately allocated exact build cgroup and bind
its actual host PID/starttime/cgroup to fresh ResourceGO before the child starts.
No cgroup namespace is necessary. Do not use guest PID1 or a translated pid as
host authorization. Namespace creation requires separate privilege authorization;
no sudo mutation command is issued in this job.

The root tree would be a NEW own rootfs under SbfInputs-20261024-v3. It must be
empty/synthetic apart from the explicit mappings in future-plan.json and the
missing public runtime allowlist below. Bind mount propagation must be made
private *inside* the new mount namespace (`mount --make-rprivate /`), never in the
host namespace. For each mapping the reviewed setup would create its synthetic
destination, run `mount --bind PHYSICAL ROOTFS/LOGICAL`, and for read-only inputs
`mount -o remount,bind,ro ROOTFS/LOGICAL`. Validate mountinfo flags, destination
owner and underlying source identity; reject source submounts or recursively
seal every one. Do not bind a broad host `/`, `/home`, `/usr`, `/etc`, `.cargo`,
`.rustup`, `.local`, `/run`, Docker socket, SSH agent or other worker directory.
The child sees original S10 path strings but their mounted contents are NEW own
outputs or frozen/prepared inputs. Host S10 paths are never opened or changed.

Synthetic HOME=/home/dombarker contains only these inputs and private writable
Cargo locks/database/tmp and rustup bookkeeping. Registry src/cache/index, source,
wrapper and compiler/tool bytes are read-only. Toolchain symlink targets must be
recreated verbatim inside the synthetic tree and resolve only to mapped public
inputs. The old logical Solana SDK and platform-tools roots remain unchanged.
A separate read-only per-file bind set is needed for host binaries, loader,
DSOs, Python stdlib/extensions, native tool headers/libraries, SDK scripts,
locale/NSS. No broad filesystem bind is an acceptable substitute. The current
Python mapping observation does not provide the compiler's mapping closure.

Use a fresh isolated proc mount for guest descendants only, private /tmp backed
by the own output area, and minimal /dev/null,/dev/zero,/dev/urandom devices as
explicit dependencies. No inherited privileged descriptors; stdin /dev/null;
stdout/stderr private receipt files. Mount/network isolation is not yet validated.
The build child would enter with `chroot --userspec=1000:1000 ROOTFS ...` after
clearing supplementary groups and privileged capabilities in a reviewed helper;
assert real/effective uid/gid and umask077 before the exact env-i command. No
root compiler/build child. The network namespace has no host interfaces/sockets;
no RPC or chain inputs are needed. Never pass parent service-inspection handles.

This is an ordered setup specification, not a runnable approved helper. The exact
host-runtime file allowlist, available capability-drop mechanism identities,
mount construction and child drop tests are UNSOLVED. A literal setup helper
cannot honestly be completed/tested from this packet alone; do not substitute a
placeholder root filesystem or claim preparation is execution-ready.

## Trace and output association

The existing pinned strace may wrap the exact clean inner command with `-f -qq
-ttt -s 65535 -e trace=%file,%process -o PRIVATE_LOG`. No -v/environment or read/
write-buffer capture. This was not tested with any compiler. Parser must track
fork/clone/exec/cwd/dirfd changes, failed probes, symlinks, resolved files, executable
interpreters/loader, and inherited fds. If abbreviation/truncation or missing
records prevent exact identity joins, stop the release gate. A list of pathnames
alone is not immutable input evidence; identities must bind to sealed read-only
views and future pre/GO/post seals. strace is observation, not pre-exec denial.
It covers direct cached build-script execution, unlike RUSTC_WRAPPER alone.

No old OUT_DIR or compiled cache enters. Default is initial cold; devnet uses only
that newly validated target. Pool retains its old distinct logical target; any
optional copy/reflink contains only newly validated outputs, with original actual
metadata preserved rather than edited to manufacture freshness. Cargo may
legitimately rebuild. Distinguish new diagnostics from cache-associated diagnostics.
All outputs and any newly generated program keys remain private; retain keys0600.
Unknown inputs, identity drift or any fixed ELF mismatch prevents release/adoption.
