# PV_ROWS10B resume D486 — conditional decompositions and source-binding blockers

**V225 and V403 remain SUSPENDED. No row is restored or closed, no privacy or
deployment premise is removed, and the privacy target is not established.
T is unchanged.** This report distinguishes conditional model results from
native association; neither model witnesses nor controlled-loader/cache tests
are honest-run deployed privacy counterexamples.

Worktree: exactly `/Users/dominic/ZK/.worktrees/pv-rows10`, sparse checkout.
Branch: `codex/pv-rows10b-20261029`, inherited candidate `05fdae5a3b`.
New modules: `PV_ROWS10B_*`. Host workspace:
`/home/dombarker/project-offloads/codex-pv-rows10b-20261029/`.
Receipts: this directory; commit list: `COMMITS.txt`.

## V225 — SUSPENDED at one exact first blocking link

**Blocker:** establish `PV_ROWS10B_Link_SymbolOrigin` for the actual admitted
runtime's `dlsym(RTLD_DEFAULT,"getrandom")` result and every callable value read
from `GETRANDOM_FN`: the selected pointer must be the intended implementation
whose source is bound to the stated syscall interface. No actual deployment
loader/library/cache provenance certificate is supplied by the retained source
and feature pins. A successful zero-length probe does not establish it.

This is the first blocked source-binding link, not a claim that all downstream
own-1 links have been discharged. It prevents an unconditional binding of this
backend to `getrandom(2)`. It is a P obligation; it must not be added to T or
silently delegated to V370. V370 retains the existing source-to-machine-code
compiler preservation obligation; it does not select a dynamic symbol.

Before: install the actual selected op129, including its complete returned
slice, inner OS error, outer failure/divergence, effects and entropy callback
association. After: that native installation remains open. The compiled new
results are conditional operation/control schemas, explicit model witnesses,
and dispatch/control helper laws. They do **not** establish full own-1 binding.
