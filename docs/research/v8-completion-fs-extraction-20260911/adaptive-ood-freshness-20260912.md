# Adaptive OOD freshness continuation (2026-09-12)

This continuation closes two deterministic/probability interfaces in the
actual lazy-oracle model.  It does not claim the complete OOD distribution or
global Fiat--Shamir soundness.

## Constructed results

`FSV7OODSourceAbsorbLinks.successful_source_absorb_links` now binds the two
authenticated OOD records to the concrete result fields
`out.afterFirstAnswer` and `out.afterSecondAnswer`.  The former existential
answers have been removed.  A successful source execution therefore cannot
be paired with stale independently supplied answer digests at this interface.

`FSAdaptiveFreshPairMass.adaptivePair_uniform_targets` treats the second
random-oracle input as a function of the first answer.  Provided the first
input is absent from the old cache, and every possible second input is absent
from that cache and differs from the first, the actual sequential interpreter
returns any fixed answer pair with exact mass

```
1 / card(Block)^2.
```

The companion deterministic theorem proves that the two installed coins are
the returned answers and that exactly two unread tape cells are consumed.
Cached answers are not included as fresh coins.

`sourceSqueeze_uniform_targets` instantiates the result for the literal
`digest || 1` output request and `digest || 2` advancement request.  Their
byte-level inequality is proved, and reachable history validity derives both
cache misses from chronological-prefix absence.

## Why this matters

The second Aspis OOD state depends on the first OOD answer.  A product law
that froze the second input before observing that answer would not model the
source.  The new theorem permits this adaptivity directly.  It does not infer
independence from domain labels.

## Exact remaining OOD obligation

For each source squeeze in the bounded first and distinct-second samplers,
prove the causal alternative:

1. its full 33-byte input is absent from the chronological prefix and hence
   receives the fresh law; or
2. the corresponding 32-byte digest is already in the prefix's explicit
   `priorTargets` set and is charged as an adversarial prior-target event.

This must be iterated through retry, canonical-decoding and abort branches and
then connected to the exact four-limb QM31/circle decoder.  The present result
does not condition away exhaustion or repeated inputs.

## Evidence

Both leaves were checked with pinned Lean 4.32.0 on the NUC in separate
systemd user scopes with `MemoryHigh=9G`, `MemoryMax=10G`,
`MemorySwapMax=0`, `RuntimeMaxSec=600` and Lean `-M8192`.  Exact command,
resource, hash and axiom records are in:

- `results/v8-completion-fs-extraction-20260911/adaptive-fresh-pair-v1/report.json`
- `results/v8-completion-fs-extraction-20260911/ood-source-absorb-links-v2/report.json`

Each promoted theorem uses only `propext`, `Classical.choice` and
`Quot.sound`.  No proof bytes, verifier checks or protocol ordering changed.
