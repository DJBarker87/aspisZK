# D570 V197 faithful parser correction — release checks pending

Branch `codex/pv-rdcd5-20261101`, exact worktree
`/Users/dominic/ZK/.worktrees/pv-rdcd3`, base
`a9aa230d1e9be0502b0e755540be7d22b2efd6ab`. No merge or push.
Session 2 recovery is recorded in RESUME-SESSION2.json. Every pre-existing
host attempt matched the local receipt and no task scope remained live.

## Consumer census and correction

CONSUMERS.md classifies every executable consumer across the pinned candidate,
local and remote refs (107 entries,77 distinct revisions), including reverse
imports and audit wrappers. CONSUMERS-census.json, CONSUMER-variants.json and
the complete supplemental ALL-REFERENCES-census.json retain literal git grep
results. Historical receipt references remain historical evidence. Other
branches were read only. No restored row depended on the wrong failure kind.
The kind-sensitive V197 local short_failure and diagnostic/replay are explicitly
corrected and will be rechecked. The historical counterexample is preserved
verbatim in BEFORE-sources.json and at its original commit/receipts.

The owned BytesSource changes only its import and three range calls. The
parser-specific range uses the same ordered/bounded predicate and backing
window, returning fail.panic on an invalid range. The old shared range helper
is unchanged; V236 uses only its bounded success domain. V197's early and late
failures now return panic. The late check stays after c0's None branch.
No eager16 guard, input narrowing, error erasure or extra premise is introduced.
v197-source-bindings.json preserves the exact before/after model, three
application bodies, nine library bodies and terminal panic dispatch. The
script-checked own-1/k-prime binding is a structural argument. No new extraction,
Kani credit or machine-code proof is claimed. Native-validation-reuse.json pins
6,420 historical paired parser cases as finite validation only.

## Current verification status

Corrected range binding, owned BytesSource and bounded window proofs pass.
ParserTransport's first compile90714 failed elaboration; its source is changed
before90715. Release restoration is pending the full arbitrary-slice Result
transport, all affected consumers, coherence and final audits. No new V197
RESTORED claim is made at this checkpoint.

Endpoint premises removed/added/changed: zero. T remains exactly entropy_law,
entropy_kernel and observation. V370/D381/D386, E1/E2, real RunJoin/world,
physical observer, client route and L1/L2/L3 remain obligations. Panic text,
writer state/errors, timing, allocation and abort observations are not inferred
from the Result abstraction. No Aeneas.Std fmt credit. No production source,
soundness file, dictionary, simulator, observer or key changed.
The privacy target is not established.
