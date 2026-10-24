# ResourceAvailable preregistered criteria and design

Entry HEAD ed3227f4dae529ed61d7f63c9dbd5adb8028e953; branch
codex/cx-resource-available-20261024. Only this tools/evidence packet changes.
All formal, Rust, compiler, build, extraction, Kani, backend, ELF, consumer,
scope and new host read budgets ZERO. Local Python expected below 512 MiB.
No adoption or live authority; public live boundary unconditionally disabled.

For each complete snapshot i use checked uint64 bytes M=MemAvailable,
A=Active(file), S=SReclaimable, K=KReclaimable, K>=S. Every raw global value must be uint; each used physical global field
(MemFree, MemAvailable, Active(file), SReclaimable, KReclaimable) must be
<=MemTotal. Unused virtual totals such as VmallocTotal are not physical bounds. R=MemTotal-MemFree-sum(actual top memory-owner
currents)>=0. T=K-floor(S/2). Pair adjustedAvailable=min M-max A-max T-max R,
with checked subtraction; negative or overflow DENY. Independently compute
populated finite frontier B without any per-cell stat correlation prerequisite.
Require strictly B+Q<55 GiB, B+Q+7 GiB<adjustedAvailable, min M>Q+2 GiB.
Prospective Q>0; inside-scope Q=0 only after recorded real proc-self identity,
expected controls, ancestors and frontier binding. Offline fixtures establish
no real provenance. Full B remains charged, no cap-current credit.

Before: ResourceHierarchy evaluates full per-cell charge/debt minus eligible
inactive+half-slab credits, plus full R+B+Q+7 GiB against MemTotal. It rejects
exclusive current<0, positive exclusive component>exclusive current, signed
slab subset violations and inconsistent covered stat correlations.
After: ResourceAvailable evaluates the global inequality above. Signed derived
per-cell correlations (including current and slab/type/LRU relationships) are
retained diagnostics ONLY, because unused by this estimator. Raw malformed,
negative, missing counters, cap/current, swap/pids, owner/controller/tree,
visibility/read errors and hierarchy/membership/control races still DENY.
This changes policy and its input domain; no blanket stronger-domain or old
numeric-equality claim. Old decisions and original bytes remain immutable.

## Source reserve argument (before implementation)

Exact Ubuntu-6.8.0-147.147 mm/show_mem.c si_mem_available (lines 32-73)
uses free F, totalreserve D, active+inactive file A+I, low-watermark W and
reclaimable K, all in pages: M=max(0,F-D+A+I-min(floor((A+I)/2),W)
+K-min(floor(K/2),W)). Convert the result and components to bytes. In byte
notation each kernel half term is P*floor(X/(2*P)), with page size P; the
policy half-slab term remains floor(S_bytes/2) exactly as preregistered. fs/proc/meminfo.c defines K as reclaimable slab S
plus misc reclaimable kernel. With a coherent reference and positive adjusted
availability, clipping cannot apply (clipped M=0 cannot pass). Subtracting
A_bytes and T_bytes=K_bytes-floor(S_bytes/2) leaves
F_bytes-D_bytes+I_bytes+floor(S_bytes/2) minus both existing watermark
deductions. Thus active file and all misc reclaimable kernel are removed,
at least half S is withheld, and original kernel reserves/watermarks remain.
Subtracting full R again and charging B+Q+7 GiB adds policy conservatism even
where the kernel estimate already reflects usage. Pair min/max is <= each
individual adjusted estimate. This is an algebraic reference argument, not a
physical/reclaim/atomic/future guarantee across independent reads. Kernel
MemAvailable itself is an estimate; no running binary/source match claimed.
Constants are fixed by lead policy, not tuned from counterfactual outcomes.

## Validation and causal evidence

Test strict equalities, overflow and reserve monotonicity; malformed/missing
raw globals/stat, K<S and R<0; controller/tree/PID/visibility errors; phase,
actual controls/ancestor/frontier/self binding and races; synthetic 3/4 and
6/8 scopes charged once (also covering ancestor). Preserve signed diagnostic
counterexamples. Replay complete immutable 15,015-event input and original
report hashes/old DENY without dumping full decisions. Reuse historical
14,587-event captures and their pre-source assessments; no new host reads.
Apply new estimator to reused captures as historical counterfactuals only.
Seal exact source/dependency/input/interpreter hashes, command, exit, wall,
RSS/swap/revision and N/A axioms. Derived JSON >5 MB hash+size only.
