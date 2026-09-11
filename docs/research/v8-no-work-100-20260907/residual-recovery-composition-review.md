# Residual recovery composition: focused kernel-checked conditional bound

[ResidualRecoveryCompositionV8.lean](experiments/ResidualRecoveryCompositionV8.lean)
is GREEN on focused NUC tag `residual-recovery-composition-v8-nuc-v1`:
exit 0, wall time 3.34 seconds, peak RSS 6,890,144 KiB, zero swaps and eleven
standard-only axiom audits. The log and immutable source snapshot were
copied locally and independently checked. One harmless unused `false_and`
simp-argument warning is retained; the green source is not edited to remove
it or its historical draft header. This remains a conditional theorem,
not an accepted-event, commitment-binding, or fresh-oracle result.

The coordinator's focused V1–V4 and V6–V7 attempts failed; the
[V1 source](experiments/ResidualRecoveryComposition.lean) and
[V2](experiments/ResidualRecoveryCompositionV2.lean) and
[V3](experiments/ResidualRecoveryCompositionV3.lean) and
[V4](experiments/ResidualRecoveryCompositionV4.lean) and
[V5](experiments/ResidualRecoveryCompositionV5.lean) and
[V6](experiments/ResidualRecoveryCompositionV6.lean) and
[V7](experiments/ResidualRecoveryCompositionV7.lean) sources are preserved
unchanged. This agent made no local Lean run, NUC access, cache modification,
or earlier proof-source edit. V8 uses module depth 200 and 250000 heartbeats,
with depth 400 only on the two selected consumers detailed below. It embeds
no large rational result or concrete field-cardinality reduction.

The source has only three direct imports, all existing checked leaves:
`MiddleSimplePairMassV4`, `SelectedHigherYProbability`, and
`NestedCircleContinuationV2`. The new recovery classifier is deliberately
not imported: the remaining source event and high-residual estimate are
explicit hypotheses, not silently asserted consequences of another leaf.

## Product obstruction and pair mass

The caller passes the SAME pre-OOD middle polynomial E, its nonzero proof,
and its degree bound 65061549. `productObstruction c1 c2 E` multiplies it by
the fixed `SelectedSingularOODFamily.obstruction c1 c2`; it does not make a
new choice of middle E. This named definition is reporting-only in V8.
Every proof interface uses the literal product
`E * SelectedSingularOODFamily.obstruction c1 c2`, avoiding definitional
transport across the wrapper.

- `Generic.product_nonzero_degree_generic` proves nonzero and the sum
  degree bound over an abstract field and arbitrary polynomials. The
  selected pair-mass proof instantiates it with E and the fixed singular
  obstruction, deriving degree at most `65061549+25345827=90407376`.
- `Generic.pair_product` proves inclusion of either original two-point
  root event in the product two-point event. It does not assert the false
  reverse implication: mixed roots at the two points are permitted.
- `Generic.product_outside_generic` derives BOTH original non-pair
  hypotheses for abstract E/F. The conditional selected LOW consumer
  inserts the fixed singular obstruction only when applying that theorem.
- `exists_product_roots` constructs the complete admissible root set;
  `Generic.product_roots_card_generic` bounds its cardinality from the
  abstract product's nonzero/degree facts. The selected mass proof feeds
  those facts directly, without a standalone selected polynomial wrapper.
  The same set and polynomial are passed onward, with no post-sample filtering.
- `product_pair_mass` combines
  `RootSetPairMass.actual_one_call_target_bound` and the existing generic
  `MiddleSimplePairMass.Generic.pair_cap_mono`. It gives

      targetMass <= D*(D-1)/(N*(N-1)), D=90407376,
      N=RootSetPairMass.domainSize.

The actual ordinary decoder success mass appears in the explicit
`NestedCircleMass.Generic.Uniform` hypothesis. Aborts and the arbitrary
between-answer history update are preserved. The result is not a claim
of Fiat--Shamir freshness or an independently uniform source sampler.

## Exact gated high/LOW partition

A proposed recovery predicate may depend on gamma, kappa, tau, and alpha;
the only structural premise is that it implies the actual `HighPrefix`.
The intended instantiation is SAME-Q high-witness recovery to the fixed
family's own-supported tuple, as described in the separate
[arithmetic/composition report](residual-recovery-probability-review.md).

`Generic.gated_partition` proves the pure weighted identity

    1[higher and not recovered]*weight
      = 1[high and not recovered]*weight
        + 1[higher and not high]*weight.

Here high implies higher and recovered implies high. No disjointness or
probability premise is supplied: the two branches are disjoint by their
definitions. `pointwise_partition` specializes this identity to the SAME
actual suffix; `probability_partition` applies the four original finite
averages. It preserves the actual adaptive final and the original domains.

The new, namespace-local `residualProbability` definition means precisely
the higher-prefix payoff gated by not recovered. It is NOT declared equal
to any earlier residual probability or the literal verifier's accepted
event. The actual no-good/lower-degree/source/authentication branches need
their own deterministic inclusion or separate accounting.

## Conditional non-pair and terminal consumers

`conditional_nonpair_bound` assumes outside the product pair event and
the explicit pending high-residual bound

    highResidualProbability <= 104/Gamma.card.

It derives the singular non-pair hypothesis and reuses
`SelectedRegularLowProbability.low_probability_bound`, obtaining

    residualProbability <= 117153/Gamma.card
      + integratedBudget(q,Gamma,A) + q/G.card + 18/A.card.

The exact LOW theorem's checked geometry, nonempty domains,
`Gamma.card>=6752623450`, and `0<q<=262144` premises remain visible.
The `117153` is `104+117049`, not a second common-root charge.
`integratedBudget` already contains its conservative cubic `3/A.card`.
Only LOW spends the shared `q/G.card+18/A.card` suffix repair, once.

`conditional_continuation_bound` accepts an arbitrary terminal-history
reward and the explicit bound

    reward(first,second,terminal) <= 1[(first,second) in S.offDiag]+b.

It uses `NestedCircleContinuation.actual_exception_bound` and the product
pair theorem to derive `pairPay <= pairBudget+b`. It retains a nonempty
finite coin set, history-uniform ordinary law, complete root set and a
nonnegative b. It does not invent a Rust-to-Execution constructor or infer
the displayed event implication from verifier acceptance.

The next source adapter must instantiate recovery with the actual SAME-Q
family event, derive the explicit high-residual bound from
`SelectedMiddleImageRecovery`, supply the terminal unit/source-coordinate
case split, and identify its target payoff. Those connections are not
claimed by this deliberately conditional leaf. No new gamma cardinality
or large arithmetic proof is duplicated here.

## Preserved failures and structural replacement

V1's two generic declarations checked successfully, but three concrete
polynomial specializations reached depth 200: `product_nonzero_degree`,
`product_outside`, and `product_roots_card`. As authorized by the coordinator,
V2 puts `set_option maxRecDepth 400 in` around ONLY these three declarations.
The module-wide setting, heartbeat and resource caps are unchanged. No
mathematical hypothesis, event, or bound changed.

V1's selected pointwise partition could not consume the generic identity
by definitional conversion to `LowPrefix`. V2 uses the already checked
`higher_partition` interface and explicit recovered/high/low case splits,
following `SelectedHigherYProbability.pointwise_partition`. Both sides
still contain the SAME suffix; no direct unfolding of the concrete final
or recurrence is introduced. The final continuation inequality now uses
`simpa only [add_comm]` to align its added constant. No generic theorem
was rerun by this agent. Exact V1 runtime/receipt data remain with the
coordinator and are not invented in this draft report.

V2 cleared every partition and composition error. The coordinator reports
that only the same three selected polynomial lemmas still exceeded their
local depth 400, with no other source errors. V3 changes ONLY those three
settings from 400 to 1000, under explicit coordinator authorization based
on the established selected-polynomial elaboration precedent. The scope
remains exactly `product_nonzero_degree`, `product_outside`, and
`product_roots_card`; the module depth stays 200 and neither heartbeat nor
memory/cgroup caps change. The V2 proof repairs and every theorem statement
are preserved byte-for-byte apart from the draft header and these settings.

V3 still hit the same selected-polynomial depth failures at 1000. No further
increase was authorized or attempted. V4 instead removes the three failing
selected wrappers and their audit targets. Their replacements are abstract
field lemmas for product nonzero/degree, outside-product pair inclusion,
and root cardinality. The selected pair-mass consumer obtains the existing
`fixed_cover` facts, applies the generic product lemma to E and a local
abstract F, and feeds the resulting product facts directly to the generic
root-cardinality proof. The selected LOW consumer directly uses the generic
outside implication. All other partition/composition proof bodies are
retained. There are still eleven intended audits, now including the three
generic replacements rather than the discarded selected declarations.

V4 checked all abstract-field product lemmas and the partition/probability/
continuation declarations. Only the two selected applications,
`product_pair_mass` and `conditional_nonpair_bound`, hit depth 200. Under
the coordinator's focused authorization, V5 adds declaration-local depth
400 to EXACTLY these two consumers, placing the option before the
nonpair theorem's documentation comment. There are no proof or statement
changes. Generic proofs, all other selected declarations, and module
settings stay at depth 200; heartbeat and resource caps are unchanged.

The coordinator's V5 preflight flagged the placement of the documentation
block between the nonpair consumer's local option and declaration. Before
any reported V5 compile, V6 converts that block to an ordinary comment and
moves it above the option. Both `set_option maxRecDepth 400 in` commands
now immediately precede their theorem commands. There is no proof, bound,
hypothesis, or resource-setting change in V6; V5 remains preserved.

V6's focused run confirmed the options applied, but its two remaining
selected consumers still exceeded depth 400; the coordinator reported no
other source errors. V7 changes only `product_pair_mass` and
`conditional_nonpair_bound` from local depth 400 to 1000 under explicit
coordinator authorization. Both options remain immediately before their
theorem commands. All generic facts and other declarations remain at module
depth 200, and no proof body, hypothesis, bound, heartbeat or memory cap
changes. V6 is retained unchanged.

V7 established that raising depth did not resolve the two remaining
failures: they occurred while transporting the selected
`productObstruction` wrapper to the generic polynomial expressions. V8
replaces every theorem hypothesis/use of that wrapper with the literal
product, including the complete-root and nonpair interfaces. The wrapper
definition remains only for reporting and is never used by a proof.
The two local settings return to 400; there are no further depth increases.
The ordinary local `F` alias in the pair-mass proof names precisely the
literal singular polynomial. No mathematical object, polynomial bound,
source/event premise or probability charge changes. V7 is preserved.

V8's literal-product replacement cleared the remaining failures. Its
eleven audited declarations contain only `propext`, `Classical.choice`,
and `Quot.sound`, with no `sorryAx`. No proof source was modified after
the successful run. V5 remains a preflight-only source revision, not an
invented compiler attempt. Earlier failed sources remain separate and
their failure descriptions above are not counted as theorem credit.

The checked generic facts operate on polynomial products, propositions,
and rational means. Exact arithmetic of the final selected parameter
instance remains in `residual_recovery_probability.py`, whose independent
Pascal/telescoping checks already pass; it is not an imported proof.

Static inspection checks declaration/namespace dependencies, the two-point
event direction, and same-suffix ordering. A source scan finds no `sorry`,
`admit`, `native_decide`, or newly declared axiom. The successful focused log
was parsed independently: exactly eleven axiom arrays were found and every
entry belongs to the three standard axioms above. Prior arithmetic records
and concurrent files remain frozen. No unchanged Lean replay is needed.

## Exact green-run evidence

The following local receipts are the exact files supplied by the coordinator:

- [V8 log](experiments/residual-recovery-composition-v8-nuc-v1.log), SHA-256
  `4041c1d9bd56c26f7b7003e459e180d63e266e904d3fd4539599946bd487e7b6`.
- [V8 source snapshot](experiments/residual-recovery-composition-v8-nuc-v1-source.txt),
  SHA-256 `108953bd2bd14b085c45194d7c1262914ece938731b8b60b9a32a29da724ed3a`.
  This is byte-identical to the frozen `ResidualRecoveryCompositionV8.lean`.
- [V8 run manifest](experiments/residual-recovery-composition-v8-nuc-v1-manifest.json),
  SHA-256 `7a86fab7342910b25269102931b9cc1e9afd290fe4154d541fb7eef80641258f`.
- The successful log records `.olean` SHA-256
  `3ea99bc631c30536e1ead985e09f7e17bda3db075166892b2c9d87074e42c76b`.
  At this report's verification boundary the binary was not copied into
  local EX; this is a logged remote post-run digest, not an independently
  rehashed local binary. The source/log/manifest receipts are local.

The manifest has 1071 registered files. Both log preflight and postflight
report `OVERLAY_PROVENANCE_PASS=1071`, followed by
`PROVENANCE_UNCHANGED=true`. This verifies registered entries; it is not
a new complete native-package replay or proof that every transitive cache
entry was registered. The three direct imports do have both source/output
entries, and their source digests independently match the local files:

| Direct import | Source SHA-256 | Registered output SHA-256 |
| --- | --- | --- |
| MiddleSimplePairMassV4 | `75006b35426490f43ef308ff3bf1123e34b37917ae8ac1d46bc7023a9eeb6bf3` | `657895071b918ed0ffa7d0fffd6dd933cdb9688a9e11088ad54cdc026737dde5` |
| SelectedHigherYProbability | `598cdd2f23f2e8276e7a9785936f4b627f9f5c1e39a9557b237325ffd41ddcfa` | `aac729362082eed82a123b8511b040765b5854441099fba368ee2b1a3b41393b` |
| NestedCircleContinuationV2 | `b41d00c49af2e157eacb3ea26aaed82e184f0f469b750e57b9b9000cccea606d` | `adb6e41d3d5eced350b8829544c6971c48b9f59021c599526594960caf618f54` |

The source-work baseline is `7c8e18488f1337b1ff247908a1a8e86325ec29bb`.
The inherited runner creation pin is separately
`289d7356c78a4cd493fe61a54f9548f2a0c11298`; borrowed V7 pin is
`26a9cd4718aae9f9de7ef1c3394fb74a229085d5`. These old cache pins are not
a claim that the new source belonged to those revisions. Lean is 4.32.0,
commit `8c9756b28d64dab099da31a4c09229a9e6a2ef35`; Mathlib is pinned at
`81a5d257c8e410db227a6665ed08f64fea08e997`.

The coordinator ran the existing Tailscale NUC task
`/home/dombarker/project-offloads/aspis-higher-y.fMoMeX`, using the actual
network endpoint `dombarker@100.108.41.90` (the `nuc.local` host-key alias
is not the transport endpoint). The focused command in the log is

    lean -j1 -M9500 -R TASK/overlay -o TASK/overlay/ResidualRecoveryCompositionV8.olean TASK/overlay/ResidualRecoveryCompositionV8.lean

The timed compiler ran in its own recorded systemd scope with
`MemoryHigh=8589934592`, `MemoryMax=10737418240`, `MemorySwapMax=0`, and
`cpu.max=200000 100000`. Its runner SHA-256 is
`5780e61b4d286905ab912bb6ab8e103a20908f78c11bea415db40a5fad110e52`.
The report updater used only local read-only hash, snapshot comparison,
manifest and log checks; it did not launch another compiler or touch the
NUC. No global endpoint or grinding term was added.
