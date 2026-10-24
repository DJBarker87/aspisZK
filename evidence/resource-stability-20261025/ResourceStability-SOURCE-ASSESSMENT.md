# ResourceStability source assessment before implementation

Read /Users/dominic/ZK/AGENTS.md fully and supplied r1p-common.txt. Specified
local-lean.txt is absent; the v2 assessment independently records its absence.
Current manager instructions supersede stale common-file allocation details.
Read immutable merged Available candidate (scan, validate_membership, observe,
membership) and complete GO evaluate/bind_scope/live-disabled statements;
Admit source loader, adapter, audit; Available criteria/assessment/report;
initial and v2 Admit criteria/assessment/report/failures; v2 exact race detail
and full replay receipt. No live worker, host, cache or session A inspection.

Primary reference provenance is REUSED, not newly fetched (offline budget):
Linux 6.8 official cgroup-v2 documentation
https://docs.kernel.org/6.8/admin-guide/cgroup-v2.html ; exact Ubuntu tag
Ubuntu-6.8.0-147.147 memcontrol.c and page_counter.c as identified by immutable
ResourceStat primary-source-hashes.json (b705abea50a0f8ff094b2a51e1357f7c6b04681d857dda7c9af4e12583970d0d,
fa75f772be13a4b3905182e023d573ecba9f066361e3065e4c1d0108216196cb).
Read ResourceStat ASSESSMENT and ResourceHierarchy SOURCE-ASSESSMENT completely.
No new primary-source fetch or kernel binary/source identity gate is claimed.

Relevant documented semantics: memory.max limits a cgroup's hierarchical
accounted usage, not an enumeration-dependent sum of resident process estimates;
memory charges belong to the charging cgroup and migration/exit does not
instantaneously transfer or erase all charges. A process-list delta therefore
is neither a charge nor a refund. Limits are not a physical instantaneous
future guarantee (some circumstances permit exceeding them). Stable controls
and a full reservation frontier are indispensable; stable unrelated TIDs are
not an additional numeric reserve term. Root residual retains unaccounted
usage; controller-disabled groups stay with their memory owner. Population
changes remain structural denials because they can change the frontier.

Exact source dependency assessment: observe selects frontier by ordered
path/enabled/populated/cap and ancestor coverage; sums FULL caps into B.
R reads only MemTotal, MemFree and top memory-owner currents. Aadj uses only
R and global M,A,K,S. Membership IDs are consumed by validation and diagnostics,
not these numerical expressions. pids.current validates full subtree thread
counts, so it may change only consistently with the complete snapshot. New
projection must retain every old structural/control field and explicitly root;
only task identities/memberships leave the cross-snapshot equality predicate.

Noninterference claim: conditional on each snapshot independently passing all
validation, equal numerical inputs, equal structural/control projection and
same validated collector identity imply equal B,R,Aadj and cap/reserve results
under changes solely to unrelated memberships. The conclusion is NOT hidden
in a premise: hypotheses are raw field equalities and validation, not equal
outputs. This is a source/data-dependency argument, not Lean or security proof.
Narrow policy change is justified at that level only. It weakens one identity
stability condition and strengthens prospective self binding; no blanket input
domain ordering is asserted. No native/security/trust assumptions discharged
or added. Old errors and bytes remain unchanged.
