# Source-derived finite requirements and retained boundaries

These requirements describe immutable SbfLinux at 9f50be799e. They were not
executed against Linux. Exact complete FIXED_PROBE text and argv are retained
in SbfRuntime-source-inputs.json, derived from AST data without executing the
backend. All assumptions remain; no before/after theorem premise change.

Ordinary source imports are errno, fcntl, json, os, stat, time, hashlib,
ctypes, platform, resource, signal and threading. Runtime metadata acquisition
also uses sysconfig and struct. The actual observation imported the stdlib
modules, including ctypes' ordinary native-loader initialization; it never
imported backend definitions or called CDLL/PyDLL/syscall itself. Incidental
observer dependencies in the snapshot cannot be called a minimal guest closure.

The interpreter entry is /usr/bin/python3 with -I -S -B -c and the exact fixed
probe. The fresh resolved binary /usr/bin/python3.12 matches historical
SHA-256 e50d468e8b0adfb05733f5b87b3cff34829c4a8c1aea50c865aa8bdfe4bb150f,
8020928 bytes, CPython 3.12.3. Its ELF PT_INTERP is
/lib64/ld-linux-x86-64.so.2. Program headers, DT_NEEDED, SONAME and RPATH/RUNPATH
are parsed from retained bounded bytes in Python; this is metadata, not ELF
semantics. Each actual mapped file was paired by device/inode/offset with its
stable disk hash before the later PT_INTERP failure. The partial maps include
native dependencies and a mapped gconv-modules.cache: codecs/locale/native
configuration inputs cannot be assumed absent. No memory contents were read.
The complete loader chain and guest loader lookup locations remain missing.
The partial candidate keeps observed physical paths and explicitly proposes a
regular byte clone for /usr/bin/python3; no guessed loader/stdlib aliases were
inserted. It is NOT eligible or approved.

Both module __file__ and __cached__ are exported, including missing cached
paths. Actual successful post-hook import opens are retained separately.
Source bytes, cached pyc bytes, 16-byte magic/flags/hash-or-timestamp headers,
and timestamp/size comparisons are separate records. A frozen module's disk
__file__ is an observed associated file, not proof that disk body executed.
-B suppresses writes only; no claim excludes cached reads. Bootstrap before
hook installation, native/unmapped opens, hash-based pyc validation and actual
executed-body binding remain OPEN. No pyc unmarshalling or body execution ran.

Future root setup must reserve sealed empty /dev and mount targets /tmp /proc;
rootfs is read-only/nosuid/nodev, private propagation required, only three guest
mounts. /tmp is an independent tmpfs <=1048576 bytes, <=64 inodes, root-owned
1777 and nosuid/nodev/noexec. /proc is private for guest PID1 and read-only,
nosuid/nodev/noexec. Required interfaces include /proc/self/status, cgroup,
mountinfo and fd listing, /proc/1/ns/pid and /proc/self/ns/pid. Own pidfd fdinfo
must bind the host child PID; preexec namespace inspection requires mnt/net/pid/
user namespace objects. This job reads only own maps/status and guard lineage
metadata, not these backend control interfaces; kernel behavior is untested.

The helper must be single-threaded, use the actual gated CPython fork, retain
an owned pidfd, release only its direct child and reap it on failure/cancellation.
Postexec must be PID1, have exactly IDs 1000, no supplementary groups, zero
Inh/Prm/Eff/Bnd/Amb capabilities, and NoNewPrivs=1. Guest limits are NOFILE=256
and FSIZE=16384, after high descriptors are closed, without increasing limits.
stdin is a retained read-only null character device (1,3); stdout/stderr are
retained write-only root-owned single-link regular 0600 files. Only fds 0/1/2
survive; each output <=16384 bytes, stderr empty and stdout exactly the fixed
public JSON. No actual guest or output-equivalence conclusion was tested here.

Producer assembly remains a separate missing deliverable: exact current
collector/executable/control/ancestry pins, current admission and scope,
sudo/monitor/helper lineage, owned cancellation and parent/child postexec tests.
No old metadata GO authorizes it. The next finite data allocation must review
the intermediate /usr/lib64 alias handling, preserve the full failed chain,
and account for loader/cache/opened-unmapped inputs. A separately authorized
actual finite trace/probe must then test conditional runtime closure and the
private proc/resource/stdio/cancellation checks. There is no activation API,
allow-callback or root route added here. SDK external criterion is UNENTERED;
both deployed targets remain NOT ESTABLISHED.
