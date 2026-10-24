# ResourceHierarchy criteria and design (before implementation)

UNADOPTED offline source/accounting candidate. Base 5756082d85e4d6784de4566059d6a9845604342a.
Only new files in the two assigned directories. No host reads, SSH, process
scan, scope, builds, compiler, Rust, Lean, Kani, manifest, ELF or consumer jobs.
Local Python below 512 MiB. No adoption or current admission authority.

Before: ResourceStat requires raw unsigned counters and U=current(parent)-sum
current(direct enabled children)>=0; every E[k]=stat(parent,k)-sum stat(child,k)
must be unsigned and <=U. Slab subsets must fit kernel. An uncovered D>U cell
uses max(U,D) and zero credit. Covered inconsistencies deny.

After: exactly one contract exception: REQUIRED derived signed E[k]<0 may be
handled only in an uncovered cell. Raw values remain uint64; child sums checked.
U remains nonnegative. Every positive E[k]>U and signed slab subset contradiction
still denies. Let N=sum max(0,-E[k]) over REQUIRED, Dplus=sum max(0,E[k]) over
inactive_file,active_file,anon,kernel, all checked uint64. If any E[k]<0,
C=max(U,Dplus)+N checked; all cell credits zero. If no negative, old formula
unchanged (including positive sum fallback). Covered negative cells deny.
Retain signed E, all raw parent/children values, N, Dplus, padding C-U and original
failure provenance. No negative raw number becomes valid. Slab/kernel interactions
that contradict the old subset inequality remain denial.

Pair rule unchanged: max snapshot C, zero BOTH credits if either falls back;
otherwise old minimum credits. Full raw root residual is unchanged; padding
is additional. Strict B+Q<55 GiB, 7 GiB control, MemAvailable>Q+2 GiB, finite
ancestor/count-once/empty charged/threaded owner and actual proc self binding,
positive prospective Q and zero actual GO remain unchanged.

Algebra: N>=0, C>=U, C>=Dplus, C>=N. For old accepted pairs N=0, E>=0,
Dplus=D; old accounting and pair expressions identical, except schema and new
diagnostics. For new fallback pair reserve=max(Ca,Cb)>=each U and Dplus; credit
zero. This is a fact about recorded quantities. N is NOT an error bound on
unseen usage. No output equivalence or safety result is assumed in a premise.
Half slab/reclaim estimates on other cells remain estimates, not guarantees.

Validation criteria: immutable original 15,015 ordered event replay reconstructs
original input/report hashes and DENY; separate new decision on same snapshots.
Measured -14,086,144 cell in both directions. Arbitrary component negatives,
debt/charge overflow, negative U, positive individual, subset, covered, current>cap,
raw negative/missing/read error, controller/PID/membership/scope/legacy denials.
Both-credit suppression with consistent opposite snapshot; full root padding.
Exact numeric preservation for previously accepted synthetic/recorded pairs,
and old 4096 sum case. Reuse historical 57/64/13 receipts explicitly; no claim
of new coverage from them. Counterfactual 1/2/3/4/6/7/8 GiB on reused pair only;
current headroom UNKNOWN, no tuning or live retry. Full audit entrypoint must be
nonmutating offline and retain exact measurements/hashes/interpreter receipt.
