Source interface inventory and retained assumptions

Candidate scan: /proc/meminfo (all kB fields; MemTotal/MemFree/MemAvailable
required by accounting); every hierarchy directory via non-symlink scandir;
cgroup.type before membership and again after children; cgroup.controllers,
cgroup.subtree_control, cgroup.threads, cgroup.procs; nonroot cgroup.events;
pids.max/current when the parent delegates pids, independently of memory;
memory.current/max/high/swap.max/swap.current/stat when parent delegates memory.
Each listed TID requires /proc/TID/stat twice (PID/starttime), status (PID/TGID),
and cgroup (exact unified membership). Any read/identity/exit failure denies;
no task exit is inferred from ENOENT and no unknown live thread is ignored.

Root: attempt cgroup.type. Preserve its actual tag if present; only root ENOENT
selects the documented root special domain case. Require root threads and procs.
The root can also host a threaded subtree. Domain process sets must equal the
TGID union from the appropriate threads. Populated=false cannot hide direct
threads/processes; hierarchical population checks remain. pids.current must
match enumerated hierarchical threads; races and zombie/accounting discrepancies
can therefore conservatively deny. Membership enumeration is observational,
not a proof against all possible ABA/migration races. Across snapshots compare
hierarchy/type/domain/owner, identities/starttimes, membership, controller lists,
delegation and caps; usage/component maxima/minima remain conservative.

Domain resource owner is the nearest non-threaded ancestor, distinct from the
nearest enabled memory accounting node. A threaded node cannot own or delegate
memory; disabling memory does not discard its owner's hierarchical charge.
Finite caps charge the populated outer frontier once; uncovered nodes include
empty charged groups. Root residual = MemTotal-MemFree-top accounted currents
is fully retained. No root slab/inactive credit is added. Unknown/inconsistent
values, negative residuals, missing global inputs and all earlier boundaries deny.

Legacy helpers: unchanged historical source and relative dependency; interfaces
include cgroup hierarchy/events/subtree control/memory values, memory.stat
inactive_file, /proc/meminfo, ps process visibility, systemctl running services,
docker ps and each docker inspect State/HostConfig. Their calls are instrumented
read-only without changing arguments/results; raw content/command output/errors
are retained separately. These old helpers still omit empty charged groups and
root direct residual; no conclusion of coverage is inherited from them.

All successful candidate reads include content/SHA-256; all failures include
path/errno/error. Repeated reads are retained as ordered events, not just the
last path value. Legacy commands retain argv/exit/stdout/stderr (event files are
additionally hashed in the final artifact manifest). Source/dependency SHA-256
are explicit in receipts. Derived JSON >5 MB is replaced by hash+size only.
No public metadata is assumed to guarantee complete instantaneous visibility.
No new trust assumption, adoption, reclaim guarantee or native/crypto theorem.

Failed synthetic approach retained: failed-portability-tests.{json,log} captures
8 errors in 39 tests because macOS errno.EOPNOTSUPP != Linux 95. The replacement
uses the explicit Linux ABI value for Linux-target sysfs semantics. Original
28-test receipts and all earlier host failures remain byte-for-byte in parent.
