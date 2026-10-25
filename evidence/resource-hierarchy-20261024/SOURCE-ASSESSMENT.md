# ResourceHierarchy source assessment

Read immutable ResourceStat complete candidate and GO statements, scan,
validate_membership, accounting, propose, evaluate, bind_scope, legacy_request,
and ResourceActual complete replay. No hidden output law in these interfaces.
The old unsigned derived rule correctly rejected the recorded negative; the
new exception changes policy explicitly, never rewrites that denial.

Primary exact Ubuntu Ubuntu-6.8.0-147.147 sources fetched locally over HTTPS
and matched existing ResourceStat SHA-256 and size (no running-host inspection):
- mm/memcontrol.c b705abea50a0f8ff094b2a51e1357f7c6b04681d857dda7c9af4e12583970d0d, 221526 bytes.
- mm/page_counter.c fa75f772be13a4b3905182e023d573ecba9f066361e3065e4c1d0108216196cb, 6928 bytes.
- kernel/cgroup/rstat.c 060c5fff6be477894e5a5fff962d67fe8e38007e550b92202c2e282f83a3b9f1, 16335 bytes.
URLs are the immutable HEAD evidence/resource-stat-20261024/primary-source-hashes.json
plain Launchpad URLs, tag query h=Ubuntu-6.8.0-147.147. No GPL code copied to git.

memcg_stat_format 1646-1673 flushes conditionally and reads each state separately.
mem_cgroup_flush_stats 707-768 depends on an updates threshold; it does not
create an atomic user traversal. mem_cgroup_css_rstat_flush 5778-5816 collects
pending and CPU changes per counter and propagates to parent pending state.
rstat.c 226-276 visits CPUs/groups, releasing its lock between CPUs. The comment
promising updated subtree stat after flush is not a transaction spanning later
parent and child reads, nor a lock on allocations. page_counter_charge 70-85
walks ancestors separately. Stable identities/control before/after do not
freeze these quantities. A parent read at t0 and child read after an increment
at t1 can have parent(t0)<child(t1) even if every instantaneous ideal hierarchy
is nonnegative. This abstract schedule refutes the proposed cross-time
nonnegativity guarantee; it does not identify the recorded kernel event.

Linux 6.8 official docs https://docs.kernel.org/6.8/admin-guide/cgroup-v2.html
confirm hierarchical interfaces and type versus LRU counters; upstream v6.8
source assessment is reused from immutable ResourceStat ASSESSMENT.md. Existing
primary-source receipt is reference provenance, not a new binary identity gate.
No statsum<=current guarantee, exact observed cause, or counter-error magnitude
bound is inferred. No negative physical memory or Mac firewall conclusion.

The explicit equations and preservation argument are in CRITERIA.md. They
justify recorded-integer accounting only. Retained assumptions: complete stable
visibility and controls, legacy gates, raw uint validation, U>=0, positive
individual and signed slab subset checks, covered consistency, actual current
within finite caps. No new trust assumption or hardware safety proof.
Both security targets remain not yet established; no crypto/native premise is
closed, final Kani remains 59/60, cached generation/privacy budgets unchanged.
