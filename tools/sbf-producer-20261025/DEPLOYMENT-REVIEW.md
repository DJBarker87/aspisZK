# Fixed installation and activation review — UNREADY

No install, chmod, chown, sudoers, scope, service, native call or probe ran.
`SbfProducer-installation.json` is the exact source-only file inventory. Its
destination paths, byte hashes and modes describe a proposed installation,
not an observation that those paths exist or have those properties. Directory
ancestry must be root:root and not group/other writable, opened nofollow.
Regular package files require nlink=1, root:root, exact published modes/hash.
The two installed Python entries unconditionally deny before any import.

## Fixed invocations and installation prerequisites

Root sudo grant: the exact line in `SbfProducer_sudoers.txt`, copied verbatim
into a separately reviewed root-owned 0440 policy file. It grants only the
fixed no-argument launcher; `""` forbids arguments. There is no root Python,
shell, arbitrary command, SETENV or interpreter-argument grant. The launcher
executes only fixed env-i and Python -I -S -B with a fixed script. The shell's
startup, env, Python interpreter, ELF loader and libraries remain runtime
closure obligations. Sudo policy matching and installed policy/plugin behavior
have not been exercised; no `visudo` or sudo call ran.

The literal user-unit argv is `SbfProducer_package.SCOPE`. It names
SbfProducer-20261025-tiny-v1.scope with MemoryHigh=3G, MemoryMax=4G,
MemorySwapMax=0 and TasksMax=64. Inside it the user producer's sole subprocess
argv is `/usr/bin/sudo -n -- /usr/local/libexec/SbfProducer-20261025-tiny-root`.
The root operation takes no arguments, reports, runtime path or code input.
No scope command was executed. Future scheduling must check aggregate populated
reservations below 55GiB and obey the lead's shared-lock/window rules.

Prerequisite directories (all future, not created here):

* `/opt/aspis/SbfProducer-20261025-v1`: root:root 0555; root-owned nonwritable
  ancestry, finite package inventory only. `runtime/` also root:root 0555.
* `/var/lib/SbfProducer-20261025-v1` and `journal-root/`: root:root 0700.
* `/home/dombarker/SbfProducer-20261025-v1-journal`: uid/gid 1000, 0700;
  never consumed as root authority. Exclusive journal names enforce one shot.
* `/var/lib/SbfProducerSeal-20261025-v1` must be ABSENT. The renamed reviewed
  capture creates its own exclusive 0700 rootfs/public-output layout; it never
  adopts an old tree. This distinct capture path is part of the fixed manifest.

Journal files are exclusive 0600. Full raw reports/ordered input reads are
retained separately by the user and root; JSON above 5MB is exported only as
hash/size. Public collection is the copied exact tiny JSON output, at most
16KiB per stream, after actual own-child zero exit and closing parent writers.
No arbitrary root reads or user-selected output paths are offered.

## Missing publication, not a permission request

`SbfProducer_runtime.json` is deliberately absent. Its pin is an empty tuple,
which `approval()` rejects before any native call. A future reviewed published
trace must supply manifest bytes, hashes and signatures, exact source/runtime
closure (including stdlib, extensions, loaders, sudo/monitor/plugins/config,
ps/systemctl/docker and configuration), per-role executable/IDs/groups/caps,
cmdline/environment/limits/maps and permitted kernel maps, exact scope path,
host runtime snapshots and a finite root-owned guest file mapping.
No partial Runtime087 acquisition, Meta1G capture or old report supplies this.
Current default/devnet/Pool ELF pins stay unchanged and were not read/rebuilt.

`SbfProducer_activation.patch.txt` is UNAPPLIED and is only the source-entry
integration delta. It must not be applied/deployed by itself: a new reviewed
release must supply the approved runtime pin, regenerate all source and
external installation hashes, verify closure/signatures and bootstrap bytes,
review backend delta and allocate deployment/probe separately. Installed
metadata or flags cannot activate the present entries. There is no request for
Dominic's approval; the lead review and runtime gate come first.

## Cleanup, lifecycle and retained trust

`SbfProducer_backend_delta.patch.txt` records the complete before/after delta
from the exact renamed reviewed backend. Unchanged functions are byte/AST
sealed. New guest logic retains only helper pidfd at fd3 through credential
drop, rearms PDEATHSIG and polls liveness after the clearing window, then closes
fd3 and audits 0/1/2 before exec. Root termination raises through owned-child
cleanup; pre-release EOF prevents guest setup. The helper arms parent-death
SIGTERM against its actual sudo/monitor parent using a stable handle check.
The user resident guard tracks helper AND descendants, not only a marker.

SIG0 permission is not proof that LSM permits SIGKILL. User guard attempts to
signal root descendants may fail with EPERM; failures remain in its receipt.
PDEATHSIG behavior across namespace/credential/exec transitions, abrupt parent
death, monitor orphan/reparent paths, pending signal races and actual reaping
are OPEN native validation obligations. SIGKILL may await D-state completion;
cleanup waits may be unbounded and no bounded reap or continuous headroom is
claimed. The sampled guard cannot guarantee future physical availability.
Failure retains capture/journals; owned FDs close, own children only are waited
and signalled via pidfds. No unlink or key cleanup exists. Deleting retained
state is outside this candidate. Root adversary, kernel, sudo, CPython/native
loader and full runtime isolation remain the reviewed backend's trust boundary;
mock tests discharge none of them. No formal premise or security target changes.
