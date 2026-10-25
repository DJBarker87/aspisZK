# SbfRuntime handoff

Branch codex/cx-sbf-runtime-20261025; entry ae091370b6c3f7bd2cba1fdc511197ff0cc90998.
All changes are confined to tools/sbf-runtime-20261025 and evidence/sbf-runtime-20261025.

Established new data: one SSH transport, exit 78, transport wall
1.113214291s. Remote finite payload wall 0.03670699198846705s;
85 freshly hashed regular files, 22203242 bytes,
12 ELF metadata records, 70 loaded module records,
17 post-hook import open events, 30 pyc files.
Fresh CPython pin equals the historical pinned interpreter; selected historical
mapped-file comparisons are retained individually in coverage.json. This is
new finite metadata, not a new artifact identity/admission/runtime gate.

Process ru_maxrss 33882112 bytes, ru_nswap
0; exact guard sampled aggregate peak
28897280 bytes, 3 samples,
one tracked TGID, no descendants, no guard error/cancellations. Full samples,
lineage, initial/final unchanged rlimits and exact commands/source/dependency
pins are retained. Sampled RSS is not continuous; cgroup pressure/peak/swap and
aggregate populated reservations were UNOBSERVED under the specific metadata
exception. No scoped/build/consumer/GO permission is claimed. Startup precedes
the resident sampling; process ru_maxrss includes its high-water observation.

The payload returned UNKNOWN/78 on exactly:
`symlink target outside public roots: /usr/lib64`.
PT_INTERP is /lib64/ld-linux-x86-64.so.2. The remaining chain was not exported;
this failure concerns the acquisition's immediate-prefix grammar and cannot
establish host runtime incompatibility. No retry, query, repair or further SSH.

The partial SbfLinux-tiny-v1 schema candidate has 86 rows,
30224170 copied bytes, 16MiB/file and 64MiB total bounds respected.
It retains physical positions and explicitly maps the pinned binary also to
/usr/bin/python3. It has no approved loader entry or guessed aliases. Missing
DT_NEEDED lookup names in these rows: libexpat.so.1, libffi.so.8, libz.so.1.
Adoption STOPPED, eligible=false, completeness=false. Module/maps observations
include incidental observer dependencies and a mapped gconv cache; native
unmapped inputs, conditional imports, locales/NSS/codecs, bootstrap and pyc
executed-body binding remain OPEN. No blanket source-only import assumption.

One local finite source/pin/schema audit checked immutable source/guard bytes,
retained pins, guard/limit/bounds and candidate structure. It reached receipt
serialization and failed on unavailable local sys.orig_argv, exit1, tool wall
0.099915875s. All preceding checks and two output writes completed; this is
not a clean exit-zero result. Its lost peak/swap/dependency metrics are marked
UNOBSERVED. Error/source retained; no unchanged regression/check rerun. Final
serialization only recovers receipts/reports and does not revalidate.

Reused: immutable 9f50be799e source and 13abf7fe51 exact guard plus historical
c7bbb274e2 selected runtime pins only. No producer/approval/CLI/source contract
changed; no assumptions discharged, added or weakened. Axioms N/A throughout.
SSH/metadata budget used 1/1. Compiler, Lean, Cargo, Rust, Kani, backend,
ELF/native proof, root/sudo/ns/mount/credential/rlimit-change/guest/RPC/key
budgets used ZERO. Kani59/60 reserved, all six old resource failures charged.
No merge/push; no keys or host stage files created/deleted.

Next deliverable: a newly allocated reviewed finite acquisition that handles
and exports the complete permitted loader alias chain, plus native loader/
opened-unmapped import coverage. Fresh producer ancestry/control assembly and
separately authorized finite cancellation/private-proc/resource/stdio/postexec
probe remain necessary. SDK external criterion UNENTERED. Both deployed
targets NOT ESTABLISHED. See REQUIREMENTS.md and FAILURES.md for exact retained
boundaries and failure interpretation; raw stdout is immutable evidence.
