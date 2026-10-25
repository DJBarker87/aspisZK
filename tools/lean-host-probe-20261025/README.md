# LeanHostProbe source-only handoff

Status: disabled; no host observation, SSH, Lean, compiler, toolchain installation,
transfer, build, or identity gate has run. Both security targets remain NOT
ESTABLISHED. This work consumes none of soundness 367/368, Kani 59/60, or private
budgets. Attempt 366's historical local elaboration is context only, not a header
proof or fresh Linux evidence. No historical evidence is adopted as validation.

## Concrete sources and claim change

Before: the assigned base has no probe in these job paths; Linux workspace,
runtime, ABI and source identity are unobserved.

After: `payload.py` implements the finite observation plan below; its direct main
raises before observing anything. `transport.py` defaults to `ALLOCATED = False`
and raises before reading source or making a capture. Its sole prospective Popen
site requires pinned source bytes, a fresh private fixed capture and a durable
exclusive one-attempt charge. These are source and mock-tested operational
properties, not a proof of remote execution, byte identity or portability. No
mathematical premise, theorem, protocol or security contract changed.

## Exact observation plan

The only absolute root for toolchain contents is
`/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0`.

- `os.uname()` machine/release, `sys.byteorder`, `struct.calcsize('P')`, current
  `os.getuid()`; fd-pinned statvfs of `/home/dombarker` gives available bytes as DATA.
- `/home/dombarker/.elan/toolchains`: at most 64 shallow names, each at most 256
  characters AND bytes. Encountering a 65th entry or oversized name denies the
  listing with explicit truncation; no second page or discovered-name opens.
- Literal toolchain files: `bin/lean`; `lib/lean/{libleanshared.so,libInit_shared.so,
  libleanshared_1.so,libleanshared_2.so}`; `src/lean/Lean/{Environment.lean,
  ImportingFlag.lean,Setup.lean,CompactedRegion.lean,Compiler/InitAttr.lean}`;
  `lib/lean/Init/{Prelude.olean,Prelude.ir,Prelude.olean.server,Prelude.olean.private}`.
  Hash and size only; numeric ELF class/data/machine from the first 64 bytes of
  the five literal executable/library files. Never invokes them or their loaders.
- `/home/dombarker/.elan/bin/lean`: metadata, or at most 4096 readlink bytes;
  never follows the alias. All other encountered aliases are likewise recorded
  and stopped, including ancestor aliases. Linux/CPython bounded readlink semantics
  are part of the trusted operational boundary, not a portable readlink API claim.
- Historical `/home/dombarker/project-offloads/r1-privacy-build-integration-20261019/`
  `run-joint.sh` and `lean-toolchain`: metadata/hash, at most 1 MiB each.
  `/home/dombarker/project-offloads/aspis-joint-20261019/sources`: directory metadata
  only, no entries or contents. Historical paths do not authorize their execution.

All traversal is component-relative with NOFOLLOW/NONBLOCK held FDs and entry
shape checks. Pre/post identity includes dev/inode/mode/uid/gid/nlink/size/mtime/
ctime; detected drift invalidates digests and derived observations. Ancestor
metadata and group/world-write flags are DATA. Regular leaf owners must be current
uid or root. Installed hardlinks are counted, not rejected or globally inventoried.
Missing/denied/cap/read-error/stale outcomes retain available metadata. No snapshot
atomicity against malicious OS/root or undetectable ABA mutation is claimed.

Hash streaming uses 64 KiB reads, <=256 MiB/file and <=512 MiB total sampled file
contents, including failed reads. Remote deadline is 9.5 seconds with a 10-second
alarm; output is <=1 MiB. Local transport has a 20-second collection deadline and
rejects combined stdout/stderr exceeding 1 MiB. No AS/DATA/RSS setters, /proc,
environment/secret/key/process discovery, config, port, firewall, namespace,
sudo/root action, recursive scan, ldd, help/version command, or dependency discovery.
CPython, SSH, OS and their runtime behavior remain trusted operational boundaries.
No remote executable, interpreter or complete dependency identity is established.

## Reviewable future action (NOT authorized or executed)

`seals.json` records disabled source, prospective body and one-line activated
transport hashes. The body is the pinned payload with exactly its disabled tail
removed and the separately pinned `footer.py.txt` appended. The prospective footer
calls `main()`; the checked-in payload main remains disabled. The sole activation
diff in `transport.py`, only after explicit lead allocation, is:

```diff
-ALLOCATED = False
+ALLOCATED = True
```

The one future local command from this exact worktree is:

```
python3 -I -B /Users/dominic/ZK/.worktrees/cx-lean-host-probe/tools/lean-host-probe-20261025/transport.py
```

Its complete future SSH argv is exactly:

```
/usr/bin/ssh -T -oBatchMode=yes -oConnectTimeout=10 -oStrictHostKeyChecking=yes -oClearAllForwardings=yes -oForwardAgent=no dombarker@100.108.41.90 '/usr/bin/python3 -I -B -'
```

Stdin is exactly `prospective_body_sha256` in `seals.json`, with no other script
or shell setup. Host identity relies on existing strict known-host configuration;
no key/config read or update is requested here. Local CPython/SSH selection is an
operational trust boundary; the local command does not certify their provenance.

Capture is fixed `/private/tmp/lean-host-probe-20261025-capture-v1`, created fresh
0700. An existing capture is a hard stop, never adopted, overwritten, deleted,
renamed or retried. Exclusive 0600 files and fsync of file/directory, plus parent
fsync, precede Popen. `charge.json` survives launch failure; failure/result receipts
(including local self/child RSS and swap counters; remote RSS/swap unobserved)
and capped output stay private. No automatic success/admission inference from JSON.
An interrupted or failed charge remains spent; fresh action needs new lead review,
not a renamed capture. Native process-creation and filesystem durability semantics
remain within the OS trust boundary. No host action can be enabled by CLI input.

## What later data could and could not support

Literal file sizes/hashes, header fields, shallow cached names, alias outcomes,
workspace metadata and historical script/toolchain hashes can inform a subsequent
Lean 4.32 workspace proposal. Missing standard-root data is not evidence of whole
host absence. Same Linux/Mac version names imply neither same bytes nor artifact
portability. Complete 9080-core identity, Core6060, serialized compatibility, native
initializers, actual source workspace, executed-byte/runtime/ABI identity and
current capacity remain OPEN. These observations supply no build-headroom GO,
whole-host inventory, proof equivalence, or general resource API adoption.

A later actual workload still needs fresh aggregate populated reservations below
55 GiB, an independent MemoryHigh=6G/MemoryMax=8G/MemorySwapMax=0/TasksMax=64 scope
(or unchanged stricter 5G/7G), and the London parallel window 22:30–14:00/global
lock otherwise. No heavy workload is authorized by this payload. No cache adoption,
cold build or unknown version selection is proposed. If actual metadata later shows
a missing toolchain, a separately pinned ordinary-user installation proposal may
be prepared; any concrete root/admin action needs separate final approval.

## Local validation and next step

Only local fresh retained fixtures and mocks are used. `validate.py` invokes the
local CPython test suite with a 30-second timeout, records exact argv, exit, wall,
source and loaded dependency hashes, interpreter hash, separate self/child RSS
peaks and swap counters. Sum of separate peaks is a conservative figure, not a
simultaneous aggregate measurement. Swap bytes are unavailable; ru_nswap counters
are reported without claiming zero OS swap usage. No memory-limit setters are used.
`axioms = N/A`, because no theorem or Lean call exists. Evidence includes the
initial 14-test receipt, the 17-test expansion and final source revision run; initial evidence is not
relabeled as validation of later edits. All fixture paths and failures are retained.

Next ONE action after lead reviews and allocates it: activate the sealed one-line
transport diff and collect this single metadata payload. Do not run Lean, install,
transfer or start any host workload as part of that action.

Frozen ELF context (not observed or revalidated here): default
`f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4`, devnet
`63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299`, Pool
`121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548`.
