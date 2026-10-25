# SbfFinite source-only design and acceptance criteria

This document precedes implementation. Base 86d9ae90c6; accepted finite input
fe20884963, candidate 30423 bytes SHA256
c69379a1f6086d66925d0ab14824a9f1c39d1a8789f8f47c8c9d183e01aa2f24.
All host/SSH/network/metadata/native/root/compiler/Lean/Rust/Cargo/Kani/backend/
ELF/probe/install budgets are ZERO. Only explicit local text/AST/hash/synthetic
Python validation below 512 MiB is authorized. No activation artifact is applied.
Public entries deny unconditionally before imports. No keys or live caches read.

The literal new schema is SbfFinite-runtime-v1, runtime version
SbfFiniteLinux-tiny-v1, root /var/lib/SbfFinite-20261025-v1/rootfs,
package /opt/aspis/SbfFinite-20261025-v1, module prefix SbfFinite.
Both new setup roots must be absent. The captured tiny postexec argv/body/env
is preserved byte for byte (including the historical SbfSeal output label).
Only root/version/module/package mappings change; no startup equivalence follows
from renaming host source. Any later body delta needs fresh runtime collection.
Each of 92 logical guest rows becomes a separate new inode, 35655597 bytes total,
82 physical endpoints. Exact source chains, alias links, identity and hashes
come exclusively from admitted immutable acquisition inputs, not caller data.

Installer: fixed noargument internal body, disabled public entry. Fresh root
owned nonwritable nofollow ancestry; no adopted staging, rename, chown, links,
clone or cleanup. Root-only O_EXCL|O_NOFOLLOW writers, regular nlink1,
complete source-chain checks before/after streaming, bounded lengths and time,
written hash then closed-writer nofollow readback. Close ALL writers before
sealing 0444/0555. Retain partial failure. Package source inventory pinned;
external reviewed bootstrap pin explicitly outside its own circular inventory.
No general root reader, shell, sudoers or SETENV grant. Future fixed noargument
administrative command documented only, never executed here.

Concrete probe reuses immutable SbfLinux9f50 / Producer20a lifecycle and full
RssGOv3 55GiB/reserve7/guard2/rawvisibility/bothscan/error policy, with exact
byte/AST rename and before/after delta records. Distinct own unit 768M/1G/0/64,
512MiB sampled guard, 115s guard/120s transport, 4MiB summary, cap counted once.
No full Producer runtime approval premise: its existing 3G/4G gate is unchanged.
Fixed user/root continuations must freshly inspect actual controls, roles and
FDs, never accept caller GO/report/manifest. Actual child zero exit precedes
<=16KiB public collection. pidfds, barriers, rearmed PDEATHSIG after credential
clear, own-child cleanup and retained capture are required. Kernel/CPython/
loader/native/LSM/D-state/orphan behavior remains open; successful observed
finite cases may return an observation rather than unconditional unresolved.

Acceptance: focused synthetic negatives for schema/argv/root/hash/size/path/
bounds/chains/races/growth/fresh-inode/writer/seal/retention, FD/role/cap/unit/
identity/permission/cancellation/parentdeath/control/exit/output. Full policy
runs on synthetic raw data with reused function identities, not unchanged whole
fixtures. Receipts retain command, exit, wall, process+aggregate RSS, swap,
source/dependency hashes and axioms=N/A. Failures remain. No formal, native,
installation, cryptographic or deployed-target closure is inferred.
Both deployed targets NOT ESTABLISHED. Finish concrete source then stop for
lead review; future native/root data and authorization are a separate stage.
