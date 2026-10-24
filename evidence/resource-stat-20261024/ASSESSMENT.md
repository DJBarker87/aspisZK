# ResourceStat primary-source assessment

UNADOPTED estimate; no kernel invariant or resource guarantee established.

## Sources and exact version

Read official [Linux 6.8 cgroup-v2 documentation](https://docs.kernel.org/6.8/admin-guide/cgroup-v2.html),
upstream [v6.8 memcontrol.c](https://github.com/torvalds/linux/blob/v6.8/mm/memcontrol.c),
and exact Ubuntu tag [Ubuntu-6.8.0-147.147 memcontrol.c](https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/mm/memcontrol.c?h=Ubuntu-6.8.0-147.147),
[page_counter.c](https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/mm/page_counter.c?h=Ubuntu-6.8.0-147.147),
[rstat.c](https://git.launchpad.net/~ubuntu-kernel/ubuntu/+source/linux/+git/noble/tree/kernel/cgroup/rstat.c?h=Ubuntu-6.8.0-147.147).
The browser could not fetch Launchpad; Python HTTPS fetched exact tagged primary
files successfully. Hashes/sizes/symbol line references are in primary-source-hashes.json.
No GPL source is copied into this packet. These are tagged source observations,
not verification of the running kernel binary/configuration against source.

## Findings

Ubuntu memory_current_read (line 6739) reads the hierarchical page counter and
converts pages to bytes. It neither reads the stat vector nor drains per-CPU
charge stocks. consume_stock/refill_stock/drain_stock (2314 onward) cache already
charged capacity on CPUs; draining returns it through page_counter_uncharge.
Stocks can make current larger than object/stat usage. This mechanism alone
cannot identify the cause or sign of the recorded 4096 excess.

Ubuntu memcg_stat_format (1646) calls mem_cgroup_flush_stats (758), which flushes
only beyond an update threshold, then reads individual state counters. Periodic
flush work is asynchronous. The threshold is an implementation optimization,
not an allowed error budget for this gate. mem_cgroup_css_rstat_flush (5778)
aggregates per-CPU deltas and propagates them to ancestors. rstat serializes
flushers, iterates CPUs and can release/reacquire its lock; it does not lock
allocators, page counters, other interfaces, or the userspace traversal.
page_counter charge/uncharge propagation also traverses ancestors separately.
No shared transaction relates a previously read current, a later stat vector,
and still later children's measurements. Equal hierarchy/control identities
across snapshots do not freeze usage or eliminate these temporal mismatches.

There is a second obstruction to calling the four terms disjoint: the official
docs distinguish type counters from LRU-list counters. Exact Ubuntu
include/linux/mm_inline.h folio_is_file_lru (28) includes lazy-free anonymous
folios; mm/swap.c folio_mark_lazyfree (726) moves these to inactive file LRU,
while mm/rmap.c tracks mapped anonymous pages using NR_ANON_MAPPED. Thus anon
and file-list categories can overlap. This is a source-supported counterexample
shape, not an attribution of the observed fitness-worker discrepancy to MADV_FREE.
The historical name disjoint_total is retained as a serialized compatibility
label only. Kernel includes slab; kernel+slab must never be summed as disjoint.

Conclusion: sum<=current across these reads is an unsupported acceptance
assumption, not a guaranteed Linux invariant. A 4096 discrepancy is neither
ignored nor classified as harmless. Missing, unreadable, malformed, negative,
overflowed, individual-over-current, slab-subset, hierarchy, membership, and
finite-cap errors remain denials even when Linux races could explain them.

## Before/after equations and premises

Before: with U=parent current minus immediate enabled child currents,
E[k]=parent stat[k] minus child stats, D=E[inactive_file]+E[active_file]+E[anon]+E[kernel],
require all existing checks AND D<=U; uncovered reserve U-I-floor(S/2).
After: retain every check except D<=U for *uncovered* cells only. If D>U,
C=max(U,D), Icredit=Scredit=0, reserve=C. Keep raw U,E,D,D-U and fallback flag.
Covered D>U remains denial; observed current>finite cap always denies.
On a pair, Cpair=max(Cbefore,Cafter); if either fallback then both credits zero;
otherwise use the old minimum credits. Root residual remains
MemTotal-MemFree-sum(actual top currents), fully charged; padding is extra.
No valid former estimate decreases or changes numerically. No output-equivalence
or memory-safety conclusion enters a premise; this is executable bookkeeping.

The useful conservative claim is relative to the recorded quantities and old
credit formula: a fallback charges at least each observed exclusive current and
both recorded D values and credits nothing. It cannot bound unseen peaks,
future allocation, arbitrary asynchronous error, or guarantee reclaim. Retained
half-slab and inactive credits on other consistent cells are still estimates.
Strict B+Q<55GiB, 7GiB control, MemAvailable>Q+2GiB, full root/empty/threaded
coverage and GO actual self binding remain unchanged. No policy adoption.

## Preservation argument

For every formerly accepted pair, each D<=U, so both fallback flags are false,
C=U in each snapshot and every old credit expression is identical. Finite
frontier, residual, B+Q and all strict comparisons are unchanged. Therefore
all numeric reserves and allowed flags are identical for these inputs (new
schema/diagnostic keys aside). For a newly handled uncovered cell, Cpair is at
least both U values, both D values, and either former individual snapshot
reserve U-credit. Pair credit is exactly zero. Extra charge is never deducted
from root residual. These are algebraic facts about recorded integers; they do
not establish a bound on physical usage between reads.
