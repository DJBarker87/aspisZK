# Linux backend review criteria, recorded before terminal candidate review

The source-only SbfLinux worker is live. Its source/output has not been read.
This document adds reviewer checks; it grants no Linux, root, probe or compiler
execution. All current security and artifact targets remain unchanged.

| Obligation | Required source/evidence | Reject or retain open when |
|---|---|---|
| Correct mounted root | Detached new mount fd remains the authority for populating and entering the new tree. Targets are opened relative to that tree. | A pre-overmount directory fd is mistaken for the new root, or later mounts populate the covered old tree. |
| Descriptor mount targets | Typed x86_64 ABI, bounded structures, explicit source and target empty-path flags, no user-controlled absolute/path interpolation. | A fd is converted into an unprotected path, or the wrong mount/object is mutated. |
| Read-only source capture | Reviewed sealed private inputs only, no inherited writable descriptor or writable alias accepted as immutable input. | Whole host caches/directories are exposed, source pinning is promoted into immutability, or real runtime closure is assumed. |
| Private device semantics | Device mounts can actually access their intended device; other mounts preserve NODEV/NOSUID/appropriate execution flags. | NODEV remains on the device mount or is recursively cleared on the whole tree. |
| PID/proc view | The first child after NEWPID is guest PID1; fresh proc belongs to its PID namespace. Host-owned child identity is distinct. | Host proc is bind-mounted, guest PID is accepted as host authority, or stale inherited proc descriptors survive. |
| Chroot and capabilities | Enter via correct root fd, chdir to new root, close every old-root/host reference, drop groups/IDs/capability sets in checked order, no-new-privileges, exact fd survivors. | Old cwd/fds permit escape, executable file capabilities remain effective, or root/helper mode is enabled without admission. |
| Owned lifecycle | PIDfd belongs to the actual fork/clone child; no unrelated reaper/thread/SIGCHLD setting can recycle it; timeout signals stable owned identity and reaps that child. | Numeric PID fallback can signal a reused PID or an escaped descendant remains uncontrolled. |
| Output | Original root-owned parent read descriptors retained; child only owns stdout/stderr writers; bounded exact payload read after confirmed child exit. | Collection reopens a user-writable path, waits indefinitely, or validates synthetic output as a real execution. |
| Source/runtime/API compatibility | Exact ABI constants and structure layouts pinned; unsupported syscall/capability/kernel paths deny. | A modern manual is treated as proof that the actual build-host kernel supports it. |
| Admission and actual evidence | Producer recomputation and source/runtime/env/limits/ancestry/scope controls are a separately reviewed gate; actual privileged CLI stays disabled. | An old marker, projected report, mocked test or source-only implementation authorizes execution. |

Primary API references consulted read-only on2026-10-25:

- [open_tree(2)](https://man7.org/linux/man-pages/man2/open_tree.2.html): detached cloned mount objects and fd-relative operations.
- [move_mount(2)](https://man7.org/linux/man-pages/man2/move_mount.2.html): separate source/target empty-path flags and CAP_SYS_ADMIN requirement.
- [mount_setattr(2)](https://man7.org/linux/man-pages/man2/mount_setattr.2.html): zeroed extensible structure, fd-empty-path scope, and NODEV device access semantics.
- [pidfd_open(2)](https://man7.org/linux/man-pages/man2/pidfd_open.2.html): fork-child PID stability depends on SIGCHLD/reaping conditions; clone with CLONE_PIDFD is the alternative when they do not hold.
- [pidfd_send_signal(2)](https://man7.org/linux/man-pages/man2/pidfd_send_signal.2.html): signaling through the stable descriptor.
- [chroot(2)](https://man7.org/linux/man-pages/man2/chroot.2.html): changing root alone does not close existing descriptors or change cwd.

These references explain API contracts. They do not attest the host kernel,
libc, compiler, source-to-native refinement, sandbox security or a successful
probe. No fresh host observation or theorem was performed. Axioms N/A.
