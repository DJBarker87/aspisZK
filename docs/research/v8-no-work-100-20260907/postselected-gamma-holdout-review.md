# Post-reconstruction gamma selection and a fresh holdout

Status: **kernel-checked finite holdout theorem**, four standard-only axiom
audits. This is not an actual Fiat--Shamir probability or extraction result.
The counterexample below remains mathematical analysis, not an additional
checked Lean target. Parent source revision:
`b2557a4b77212c77e44d29eea1b94e820bf939f8`.
New leaf: [PostselectedGammaHoldout.lean](experiments/PostselectedGammaHoldout.lean).
Only this new leaf was compiled, once, in the capped NUC scope. No source
repair, package rebuild, or unrelated-file edit was performed.

## Exact current boundary

`NestedMiddleOwnSupportDichotomy.early_member_or_all_nodes_bad` correctly
constructs one tuple from 29 gamma nodes and four actual middle witnesses at
each node. Either its C1 projection is in the early family, or all 29 nodes
lie in `SelectedOwnSymbol.badGamma` of that same tuple. The tuple is fixed
*after* those nodes, not before them.

`SelectedOwnSymbol.badGamma_card` gives

    |badGamma(p)| <= 28 * (1048576 - |own(p)|) <= 29360128.

The number 28 is a per-symbol polynomial degree, not the cardinality of the
union over symbols. Thus 29 distinct nodes do not contradict this bound.
Nor does the bound imply a small probability for previously observed nodes
when p was reconstructed from them.

## A causal ideal counterexample to retrospective charging

Let Gamma be any even-sized finite subset of a field, of size n >= 58. Fix
a balanced Boolean function f : Gamma -> {0,1} before sampling. At each
gamma the deterministic response is f(gamma); no future node is inspected.
Sample 29 distinct nodes uniformly and interpolate their responses by the
unique polynomial h of degree at most 28. Use two fixed received symbols,
whose gamma polynomials are respectively 0 and 1. The reconstructed expected
polynomial is h at both symbols.

If the sample contains both Boolean values, h is nonconstant. Both residual
polynomials h and h-1 are nonzero, so their union of roots has cardinality
at most 56. Nevertheless **every sampled node is in this union**, since
h(gamma)=f(gamma). Neither symbol is an own coordinate. The construction
uses exactly interpolation of a fixed causal response function, not an
arbitrary after-the-fact set selector.

For the uniform 29-subset experiment the probability of this event is

    1 - 2 * choose(n/2,29) / choose(n,29) >= 1 - 2^(-28).

For the inequality, condition on the first label: each of the remaining 28
draws, without replacement, has probability at most 1/2 of maintaining an
all-equal label sequence. All oracle inputs may be fresh with complete
ancestor provenance; the counterexample does not exploit any ROM collision,
prequery, failed restoration, or acceptance filtering.

This is a counterexample to **provenance plus fixed-object root-cardinality
alone**, not a source attack. In particular its per-node agreement is only
one of two symbols. It does not satisfy the actual `MiddleWitness` lower
bound of 200808 complete fibres, the fixed OOD/ordinary row gates, the
selected encoder/payment conditions, or their source timing. Proving that
those additional conditions rule out the post-selection event is still an
algebraic/support theorem; a generic FS restoration theorem cannot supply it.

## What V7 restoration does and does not add

The borrowed V7 source pin is
`26a9cd4718aae9f9de7ef1c3394fb74a229085d5`.

- `V7Tag73ConcreteRestorationClient` and
  `V7Tag73ConcreteRestorationTraceInduction` preserve actual stored-node
  provenance and adaptive parent/child histories. They do not make an object
  computed from descendants measurable at an ancestor challenge boundary.
- `V7Tag73UniqueRestorationRequests` permits reuse of immutable ancestor
  bases and excludes a non-root transition-zero refork. It is an operational
  discipline, not a bound on data-dependent exceptional sets.
- `V7Tag73OracleTableProvenance` explicitly distinguishes full ancestor
  table provenance from node-local query absence. Even complete freshness
  only supplies the fresh draw law: a target set used in that law must be
  fixed before the draw being charged.
- `V7Tag73ExactFixedK16Closure` composes actual compiler provenance with
  supplied proof-relevant stage classifiers and their bounds. The missing
  post-selection theorem would have to be one of those stage bounds, not
  a consequence of the composition arithmetic.

No generic BCS coefficient or unproved q_H multiplier is introduced here.

## Smallest sound extra check

After the entire training history, freeze p reconstructed from its 29 gamma
nodes. Draw a NEW holdout gamma from the original Gamma, after p is fixed.
For its actual recovered original candidate U, require the explicit equality

    U = ClaimTransport.batch gamma p.

Together with the selected literal-family/image conditions and
`|own(p)| < 38228`, `SelectedOwnSymbol.covered_forces_exception` then gives
membership in badGamma(p). Consequently a fresh holdout validates a
small-own tuple with mass at most 29360128/|Gamma|. The finer numerator
28*(1048576-|own(p)|) is available history by history.

This does not assume p is globally fixed: the draft accepts arbitrary
`select : History -> Candidate`. `conditional_card_le` bounds the holdout
validation set separately at each earlier history; `validation_card_le`
gives the direct history-by-challenge count, and `validation_mass_le` gives
the uniform product mass. All four declarations are kernel-checked with
only `propext`, `Classical.choice`, and `Quot.sound`.

For the actual aborting nonzero sampler, the pointwise successful value
mass is no larger than 1/|Gamma| only after the appropriate raw-tape/source
coupling is proved. Abort contributes no validating pair. Conditioning on
acceptance or selecting only successful holdouts cannot replace this
unconditional law. A distinct holdout sampled from Gamma minus the 29
training values has denominator |Gamma|-29, not |Gamma|. Repeated validation
attempts need an explicit all-attempt union or stopping bound; they cannot
be charged as one draw.

## Why this is not yet an extraction repair

A qualifying holdout can return a canonical original U different from
batch(gamma,p). That is an uncharged, separate branch. The current source
lemmas neither force equality nor show that restarting reconstruction on
that branch finishes efficiently. Adding a holdout equality test is sound
validation, but supplies no completeness or extractor-success lower bound.

To close the original branch without a holdout, one must instead prove a
source-specific stable-family/curve correspondence theorem, a genuine
common authenticated support certificate (the existing
`NestedMiddleC1Support.early_member_of_common_nodes` consumes one), or a new
causal potential argument bounding incompatible reconstructed tuples. The
actual 200808..252847-fibre middle-witness hypotheses must be used in such
an argument. Their exclusion from the counterexample is an explicit open
boundary, not evidence that the source event is probable.

## Focused verification and retained evidence

`postselected-gamma-holdout-nuc-v1` exited 0 in **0.90 seconds**, with peak
RSS **1,677,464 KiB** and **zero swaps**. The frozen source passed unchanged
on its first attempt. There were no errors, warnings, `sorryAx`, additional
axioms, or failed Lean attempts. The four successful audits are
`mem_validationPairs`, `conditional_card_le`, `validation_card_le`, and
`validation_mass_le` in `AspisV8.PostselectedGammaHoldout`.

Both registered-overlay checks printed `OVERLAY_PROVENANCE_PASS=991`, and
postflight printed `PROVENANCE_UNCHANGED=true`. These are exact registered
artifact checks; the native package cache remains a pinned inherited
boundary, not a replay of package compilation. The leaf imports only the
three native Mathlib modules shown in its source, whose source/output cache
presence was checked before the run.

Lean 4.32.0, commit `8c9756b28d64dab099da31a4c09229a9e6a2ef35`, ran with
`-j1 -M9500`. The observed cgroup settings were MemoryHigh 8,589,934,592
bytes, MemoryMax 10,737,418,240 bytes, MemorySwapMax 0, and CPUQuota 200%.
The inherited runner still records research-cache origin
`289d7356c78a4cd493fe61a54f9548f2a0c11298`, separately from this leaf's
`b2557a4b77212c77e44d29eea1b94e820bf939f8` working-source parent and the
borrowed V7 pin above.

The initial read-only preflight found an unrelated V7 Lean process, so no
holdout job was launched then. At **2026-09-10 20:51:34 UTC**, process
inspection showed no Lean/lake process and 50,046,746,624 bytes available.
The launch command checked again for either process before invoking the
runner. The unrelated jobs, VM, and existing host swap were left untouched;
the zero-swap result above is the scoped holdout job's GNU-time statistic.
After terminal postflight, the research compiler slot was released before
the immutable artifact copy and local review update.

Transport used only `dombarker@100.108.41.90` over Tailscale, with
`BatchMode=yes`, `ConnectTimeout=10`, `StrictHostKeyChecking=yes`, and
`HostKeyAlias=nuc.local`; the alias was solely the pinned host-key lookup.
The sole compile command was:

```sh
ssh -o BatchMode=yes -o ConnectTimeout=10 -o StrictHostKeyChecking=yes -o HostKeyAlias=nuc.local dombarker@100.108.41.90 'bash /home/dombarker/project-offloads/aspis-higher-y.fMoMeX/run_higher_y_nuc.sh /home/dombarker/project-offloads/aspis-higher-y.fMoMeX PostselectedGammaHoldout postselected-gamma-holdout-nuc-v1'
```

The exact source snapshot, log, manifest, and green olean were copied to
`experiments/` and locally hash-verified. The current source is byte-identical
to the retained snapshot and matches its per-run manifest entry. A read-only
local log audit verified exactly four axiom lists, each precisely the three
standard axioms, and rejected `sorryAx`, errors, or warnings.

| Artifact | SHA-256 |
| --- | --- |
| Source and v1 source snapshot | `25f615401a1b70984a90d546443663186cc611feff7441411007a93d64ac39c7` |
| Green olean | `289d03280e2880274e978eea0f7f9f1a0a28e247f12aaef6f52034c9244d3576` |
| v1 log | `9edfa919683cf947cd618d79424c94141247fdd7b5b1c812f0ce5c2d52f26887` |
| v1 manifest | `7e714aea3295ec72d6d8cb0a7b5ac2ae3f82fc1bcfbbab916e079467cc148b59` |
| Frozen runner | `5780e61b4d286905ab912bb6ab8e103a20908f78c11bea415db40a5fad110e52` |
