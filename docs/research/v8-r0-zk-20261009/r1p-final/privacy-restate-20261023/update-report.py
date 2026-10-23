#!/usr/bin/env python3
"""Refresh verbatim statement excerpts; preserve the established obligation map."""
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[4]
LEAN=ROOT/'docs/research/v8-r0-zk-20261009/lean/R1Z'
REPORT=HERE.parent/'PRIVACY-RESTATE-20261023.md'
previous=REPORT.read_text()
validation=previous[previous.index('## Validation and handoff'):]
obligations=previous[previous.index('## Stage 2: remaining real-side obligations'):previous.index('## Validation and handoff')]
old=(LEAN/'ProverCommitDeployedFuel22.lean').read_text()
new=(LEAN/'PrivacyR1HeadlineDeployedReal.lean').read_text()
def header(s):
    a=s.index('theorem privacy_headline_deployed\n')
    return s[a:s.index(' := by',a)]+'\n'
(HERE/'before.lean.txt').write_text(header(old))
(HERE/'after.lean.txt').write_text(header(new))
intro='''# Privacy endpoint against the mathematical ideal, 2026-10-23

Branch `codex/cx-priv-restate-20261023`. **The new conditional endpoint is
proved; concrete deployed privacy remains conditional on the real run join.**
Read LOG D184–D185, the root Security and proof discipline rules (especially
section 3), and the common worker/build instructions. D185 explicitly resolves
the earlier stop: the comparison contract is the ideal game with mathematical
`simE`. The prior audit and stop remain in commits `0ddade8ebd` and
`4528e0f9eb` (the obligation-map commit).
No equivalence of the two fixed ideal experiments is asserted.

## Established claim and contract choice

Added only `lean/R1Z/PrivacyR1HeadlineDeployedReal.lean`:
`R1Z.PrivacyR1HeadlineDeployedReal.privacy_headline_deployed`.
Its only refinement premise is `RustRealRefinement`, definitionally the first
conjunct of `ProverCommitDeployedFuel22.RustProverRefinement`. It compares
`rust.real` observed by `rust.observe` with `source.ideal(simE)` under the
mapped ordered observer. Both existing endpoint modules, all their definitions
and the old theorems are unchanged. No Rust, protocol, event definition or
release artifact is changed.

The theorem uses the existing `ProverCommitModelCore16.core_privacy` through
`ProverCommitReencode16.privacy_transport` for source.real ≈ source.ideal.
The real `ProverCommitFuelJoin22.test_bound` supplies the other edge.
For every adversary and every valid honest witness, triangle inequality gives

```text
|R_rust - I_source| ≤ modelError + lazyBudget(8*n1)
                     + 8/2^486 + seedBudget(2^64) + fuelCharge.
```

The proof then pads by the nonnegative already-charged ideal-side allowance
`8/2^486 + seedBudget(2^64) + fuelCharge`, and uses the existing lazy-to-fresh
bound. The exported envelope is **exactly** the old one:

```text
E = modelError W Pr L₁ L₂ + 16/2^486 + freshBudget(8*n1 W Pr+1)
    + 2*seedBudget(2^64) + 2*fuelCharge
E ≤ 1/2^109 + 1/2^137 + 1/2^454 + freshBudget(8*n1 W Pr+1)
    + 2*seedBudget(2^64) + 2*fuelCharge
E < 1/2^100.
```

No bad-event term is added, replaced, or implicitly assumed zero. Keeping the
unused ideal allowance is deliberate: it preserves the exact headline budget.

## What “old + conjunct 2 implies new” means precisely

In the old proof contract, the refinement certificate is `C1 ∧ C2`.
The compiled theorem `old_refinement_implies` proves
`(C1 ∧ C2) → RustRealRefinement` by the term `old.1`.
Applying the compiled new headline then proves
`(C1 ∧ C2) → NewHeadline(E)`. Consequently every valid instance of the old
two-join theorem also has the new headline at exactly E; there is no added
requirement. This is the precise certificate-level implication implementing
D185's “old + conjunct 2 implies new”. In fact C2 is unused in this derivation.
It does not certify the native Rust simulator, nor discharge C1 for Rust.

Distinguish that implication from a claim about isolated probability bounds.
Writing `OldBound(E) := |R_rust-I_rust| ≤ E`, C2 is an **except-bad** join,
not exact equality: it yields `|I_rust-I_source| ≤ δ_ideal`, where
`δ_ideal = 8/2^486 + seedBudget(2^64) + fuelCharge` after the existing mass
bounds. `OldBound(E)` plus that inequality alone gives `NewBound(E+δ_ideal)`,
not a same-E implication. The same-E result above is proved from the retained
C1 and the model theorem, avoiding double-charging. No same-E biconditional
between the raw old and new conclusions is claimed. Conversely, the new
headline alone cannot establish any property of arbitrary `rust.ideal`.
The earlier fixed-experiment counterexample remains valid; D185 chooses the
mathematical benchmark rather than overturning that observation.

## Quantifiers, observations, error and simulator efficiency

The universal protocol context is unchanged: `CommitHandle`, `Aux`, `template`,
`outputs`, public statement `x`, `rust`, and `observer_program`. The honest
builder is fixed as before. Within the conclusion, **every** `rust.Adversary`
and **every** `w : h.Instance` with `h.public w = x.1` remain quantified.
There is no new statement/witness domain restriction, no fixed fixture, no
restriction of adaptive observer queries, and no `Aux := Unit` specialization.

The real observable is the same full `ROMView` and Boolean observer decision;
the join demands their equality outside the same fixed realBad, seed-guess
and five-draw fuel events. It does not merely identify acceptance or roots.
`RomObserverBin.observerMap` retains `rust.observe adv` and the supplied
adaptive query program. Ordered history, duplicate queries, answers, retries,
errors and aborts must still be represented by the real join. D143's deployed
projection publishes statement/proof bytes and the adversary's oracle answers;
internal tables/audit counters are not publication. L1/L2 side-channel
transport remains a separate open obligation, not proved here.

What changes: the right experiment is source.ideal instead of rust.ideal;
its random carrier is source.IdealRand instead of rust.IdealRand; its observer
is interpreted through the existing map; the native ideal join C2 disappears.
The new headline needs no Fintype/Nonempty instances for rust.IdealRand.
The real Fintype/Nonempty context stays (Lean warns Nonempty is unused).
The old ideal-carrier instances occur only in the separate compatibility
projection lemma. E, the displayed numeric bound, and the `< 2^-100` target
are identical. The deployed real observation has not changed. Thus this
establishes the D185 simulation contract about deployed outputs, while the
old fixed-experiment theorem additionally compares a native ideal implementation.

Efficiency now concerns the mathematical simulator and ideal-game computation.
Reuse the SIM-COST results for that computation: `SimCostIdeal.run_erase`,
`SimCostRelativeIdeal.run_relative`, the primitive/representation bounds of
passes 5–6, and `SimCostOuterRetry6.scan_firstGood`/`eight_bound` (8*C+17).
These are proved cost results for the mathematical computation with their
stated preparation/decision and size hypotheses; no native sim.rs binding is
needed for the new privacy inequality. The headline itself is a probability
statement and adds no cost premise. Do not promote the existing relative cost
results to an unconditional numerical efficiency certificate for arbitrary
callbacks: D142–D143 and SIM-COST7 still require the concrete public/metadata
instance, exact Boolean P_R1 cost, representation/preparation composition and
numeric C. This work neither proves those obligations nor changes simE.

## Verbatim before and after statements

These declaration headers are extracted verbatim from the actual old and new
modules. The surrounding notations and instances are in those linked sources;
the snapshots `privacy-restate-20261023/{before,after}.lean.txt` are checked
by `audit.py`. The before statement remains in the repository unchanged.

Before, namespace `R1Z.ProverCommitDeployedFuel22`:

```lean
'''
# Write the report incrementally; subsequent append supplies each major section.
REPORT.write_text(intro+header(old)+'```\n\nAfter, namespace `R1Z.PrivacyR1HeadlineDeployedReal`:\n\n```lean\n'+header(new)+'```\n')
with REPORT.open('a') as f:
    f.write('\nThe full refinement definitions (also verbatim):\n\nBefore:\n\n```lean\n')
    a=old.index('def RustProverRefinement : Prop :=')
    f.write(old[a:old.index('/-- Every previous certificate',a)].rstrip()+'\n```\n\nAfter:\n\n```lean\n')
    a=new.index('def RustRealRefinement : Prop :=')
    f.write(new[a:new.index('attribute [local irreducible]',a)].rstrip()+'\n```\n\n')
with REPORT.open('a') as f:
    f.write(obligations+validation)
