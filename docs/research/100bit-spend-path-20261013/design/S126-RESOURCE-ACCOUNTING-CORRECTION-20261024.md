# S126 NUC aggregate-admission correction

The lead's hierarchy finding applies to this branch's older NUC launchers.
`tools/s126-sdk-modular-20261021/reservation.py` scans populated direct
`*.scope` entries under user-1000's app.slice. It omits system/Docker/VM scopes
and scopes populated only in descendants. The additional older collect-cgroups
snapshot does not by itself establish a complete host-wide historical bound.

Claims that these receipts establish a **complete historical aggregate**
reservation below the safe host limit are superseded as unverified. They
establish only the recorded subset arithmetic. This qualification applies to
past S126 native Kani, Rust, Charon/Aeneas and NUC Lean launches that inherited
these gates, including the native codec gates in the two owned-values packets.
Individual MemoryHigh/MemoryMax/MemorySwapMax=0/TasksMax, time/RSS/swap, source,
exit-status and mathematical proof evidence are unaffected. This does not
retroactively make a source packet a compliant formal release certificate.
No deployed closure was claimed, and the original security target is unchanged.

`tools/s126-host-admission-20261024/HostAdmission.py` is an exact copy of the
reviewed Port13GATE whole-cgroup-v2 inventory. Its source revision/hash is
recorded under `evidence/s126-current-caller-20261021/host-admission-correction`.
It visits populated and empty descendants, includes system/Docker/VM paths,
counts capped populated subtrees once under a capped ancestor, reports uncapped
population, and fails closed on missing required controller data. The adapted
local fixtures passed nested deduplication, empty groups, direct-zero/live-child,
system Docker visibility, uncapped visibility and missing-data checks.

A read-only host inventory at 2026-10-24 14:57:15 UTC observed 26172456960 bytes
of finite capped subtree reservations. It also lists uncapped populated VM,
service and control groups explicitly. The scanner's `admitted=true` is ONLY
its finite-cap arithmetic result. It is not authorization to start a job and
is not a bound on those uncapped groups. That current observation cannot
reconstruct a historical total.

No heavy NUC job was launched for this correction or the prepare-count work.
Before any future S126 heavy launch, use a fresh whole-host inventory inside
the shared admission lock, retain and assess uncapped populated/background
handling and current free-memory margin, and apply explicit per-job caps with
MemorySwapMax=0. Unreadable/unknown accounting must refuse admission. Historical
subset-only launchers are retained as evidence and must not be reused as a
complete admission gate. No unknown locks, cgroups or other owners' jobs were
changed or terminated.
