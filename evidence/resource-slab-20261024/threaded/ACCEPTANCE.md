Threaded API acceptance criteria — unadopted diagnostic only

Before: every node must yield cgroup.procs; any EOPNOTSUPP aborts. No
observed cgroup.type or thread/domain membership establishes the exception.
After: read cgroup.type before membership. Only observed `threaded` nodes may
substitute cgroup.threads plus verified TID/TGID identities and nearest domain
process membership for the documented cgroup.procs EOPNOTSUPP. Other errors,
unknown types, invalid domains, missing live identities and transitions deny.
Root is a documented special domain: cgroup.type exists only on non-root
nodes; record the attempted root read and ENOENT, without fabricating a tag.

Read every node's threads, domain process lists, controller delegation and
population. Verify each TID's stable starttime/TGID and unified membership;
no exit or unreadable identity is ignored. Compare the domain's process set
with the TGIDs of its own and threaded descendants' threads. Read type again
and deny transitions. Retain all successful raw reads, hashes and errors.
No blanket errno whitelist. Snapshot agreement includes observed tags,
thread/process identities, ownership, pids delegation and limits.

Memory is a domain controller; pids is independently threaded. Threaded nodes
cannot delegate or own memory. Disabled subtrees stay charged at the nearest
actual memory owner, which may be above their threaded domain. Validate both
owners separately. Read pids limits even where memory is disabled. Preserve
hierarchy/current/component/cap checks and the conservative two-snapshot
max-usage/min-credit envelope. Root direct membership and full raw physical
residual remain charged, without new residual credit. Half exclusive
slab_reclaimable remains an estimate capped at 50%; other retained usage,
7 GiB control reserve, strict <55 GiB reservation and MemAvailable tests stay.

Synthetic tests must cover documented alternate acceptance and each missing
proof, unknown EOPNOTSUPP, invalid/unknown/type-transition topology, wrong
memory/domain owners, independent pids delegation, unreadable live identities,
root membership/residual and all prior boundary/adversarial cases. Then one
read-only source-versioned before/after diagnostic; failures remain denials.
No build, scope, mutation, adoption, consumer or launch authorization follows.

Primary API specification: https://docs.kernel.org/admin-guide/cgroup-v2.html
sections Threads and Core Interface Files (consulted 2026-10-24). This is a
source interpretation, not a public-metadata guarantee of complete live data.
Formal budget ZERO; #print axioms N/A. Both security targets not established.
