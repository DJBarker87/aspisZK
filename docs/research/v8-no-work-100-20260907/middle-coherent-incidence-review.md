# Fixed-tuple middle-support incidence

Status: `MiddleCoherentIncidence` v3 is kernel-checked and frozen, with
eight standard-only axiom audits. Source:
[MiddleCoherentIncidence.lean](experiments/MiddleCoherentIncidence.lean).
Working source parent: `b2557a4b77212c77e44d29eea1b94e820bf939f8`.

## Exact source result

For one common tuple `p`, let `G` be any finite set of gammas. At each gamma,
the hypothesis gives an actual `MiddleWitness` at arbitrary later
kappa/tau/alpha and requires that its reconstructed original message equals
`ClaimTransport.batch gamma p`. The histories and retained factors need not
agree. The representation equality IS an explicit coherence hypothesis; it
is not inferred from interpolation at other nodes.

`middle_matching_803230` derives the sharp support transfer:

    4 * 200808 - 2 = 803230 original symbols.

It uses the actual witness image gate and
`SelectedRegularLowSupport.fibre_to_original_support`, including only the
proved two-symbol chord-pole loss, then the literal
`SelectedOwnSymbol.matching_eq_symbols` transport. No global no-pole
assumption, supplied codeword support, or received polynomiality is added.

For `b = own(p).card`, the generic degree-28 root incidence theorem gives

    |G| * (803230 - b) <= 28 * (1048576 - b).

`coherent_middle_card_le_36` proves `|G| <= 36` when `b < 38228`.
`coherent_37_own_support` instead proves `b >= 39932` from `|G| >= 37`;
`coherent_37_early_member` then puts the SAME tuple's C1 projection in the
fixed `EarlyC1Family.family e.c1`.

The exact arithmetic is small and symbolic:

    37 * 803230 - 28 * 1048576 = 359382,
    ceil(359382 / 9) = 39932.

At the largest insufficient own support `b=38227`, the right side is
28289772, while `37*(803230-b)=28305111`, so 37 is impossible.

The proof reuses `SupportQualifiedRootIncidence.adaptive_polynomial_bound`,
`OwnSymbolCollision.residual_degree/residual_zero_iff`, and the selected
source transports; it does not reprove V7 interpolation, encoder linearity,
or a sampler law.

## What this does not bound

The first 29 nodes represent their reconstructed tuple tautologically.
They need not be fresh relative to that tuple. A fixed-tuple cardinality
bound cannot charge them retrospectively. Even though no union over tuples
appears in the deterministic inequality, a probability application must
still fix the tuple before its tested draw, or supply a separate valid
selection argument.

In the insufficient-own branch, a tuple already represented at 29 distinct
middle nodes can have at most seven ADDITIONAL distinct coherent middle
nodes. A later middle node need not be coherent with it. Neither that
coherence nor a fresh holdout distribution is proved in this leaf.
No improvement to the self-selected 29-node event, gamma marginal,
Fiat--Shamir bound, acceptance-to-MiddleWitness gate, or payment extraction
is claimed.

## Exact swap/interpolation obstruction (mathematical audit, not a Lean target)

Here is an explicit small-code model showing why eight further middle
nodes do not automatically supply the missing coherence. Work over a
sufficiently large field, for example F257. Fix 37 distinct nonzero gamma
nodes and the 37 cyclic subsets `J` of 29 consecutive nodes. Define

    H_J(Z) = product over g in J of (Z-g),
    R_J(Z) = Z^29 - H_J(Z).

Each `R_J` has degree at most 28 because the leading terms cancel. Partition
the stored fibres into 37 equal groups, one for each J. At a symbol with
evaluation coordinate x in group J set the fixed received curve to
`R_J(Z) * V(x)`, where `V(X)=X*(X-1)` and all stored coordinates avoid 0 and
1. A concrete small domain can have 37 fibres of four distinct coordinates
in F257. The code is the scalar Reed--Solomon code containing degree-two V.

At gamma g take the actual candidate `U_g(X)=g^29*V(X)`. It agrees on
exactly 29 of the 37 fibre groups, because g belongs to exactly 29 cyclic
subsets. Thus every node has support fraction `29/37`, within the scaled
middle band. Both OOD answers at X=0 and X=1 are zero. These are fixed
degree-zero answer/helper curves, within the degree-two/degree-28 limits.

For ANY selected 29-node subset I, the interpolated message curve is

    U_I(X,Z) = (Z^29-H_I(Z))*V(X).

It matches all training candidates. At each of the eight remaining nodes,
`H_I(g)` is nonzero, so `U_I(X,g) != U_g(X)`. This holds even when two
training sets share 28 nodes: their interpolants differ by a nonzero
multiple of `H_(I intersection I')(Z)*V(X)`. Agreement on 28 nodes does not
force a degree-28 polynomial to vanish.

The tuple's own support consists only of a group whose cyclic subset J
equals I, if such a group exists. Hence own support is at most 1/37,
strictly less than 38228/1048576. Each training gamma still has many
matching non-own coordinates, so all 29 lie in that tuple's `badGamma`.
This is true for every 29-subset I of the fixed 37 nodes. Thus the
self-selection issue is genuine, not removed by overlapping-subset swaps.

The same incidence pattern can be repeated with almost equal groups at the
selected domain sizes: each gamma matches at least `29*7084=205436`
complete fibres, while own support is at most `4*7085=28340` symbols.
This arithmetic embedding is not a proof about the actual circle encoder.

Scope: this is an exact interpolation/code-support model. It is NOT a
selected interpolation-kernel factor, authenticated transcript, or valid
payment counterexample. The zero OOD sections do not prove the literal
selected row constraints. More generally, a swap perturbation in the joint
kernel of three row covectors and two OOD evaluation maps preserves those
five linear constraints; their rank alone cannot eliminate all directions
in a 1024-dimensional message space. A source-specific nonlinear/kernel
argument could still rule out the actual bad event, and remains necessary.

## Focused evidence

Only this new leaf was compiled, via Tailscale `100.108.41.90` and the pinned
`run_higher_y_nuc.sh`. The inherited research-cache pin is
`289d7356c78a4cd493fe61a54f9548f2a0c11298`; borrowed V7 source is
`26a9cd4718aae9f9de7ef1c3394fb74a229085d5`. No imports were staged or rebuilt.

Preflight found approximately 39.2 GB available on the 66.7 GB NUC. A
separate V7 service was verified at MemoryMax 12 GiB / SwapMax 0; this
leaf's 10 GiB cap brought the combined reservation to 22 GiB. The existing
host swap occupancy was not attributed to this job. The actual job scope
retained MemoryHigh 8 GiB, MemoryMax 10 GiB, MemorySwapMax 0, CPUQuota 200%,
Lean 4.32.0 `-j1 -M9500`, recursion depth 200 and 250000 heartbeats.

| Attempt | Exit | Wall seconds | Peak RSS KiB | Swaps | Outcome |
| --- | ---: | ---: | ---: | ---: | --- |
| v1 | 1 | 3.45 | 6830724 | 0 | Generic filter inference selected a different decidability instance; source support transport already audited standard-only. |
| v2 | 1 | 3.67 | 6832212 | 0 | Adding a local classical tactic alone did not resolve the same two filter seams. |
| v3 | 0 | 3.78 | 6864264 | 0 | Explicit propositional membership transport fixed the seams; all eight audits standard-only. |

No mathematical premise or resource limit changed. Failed attempt snapshots,
logs and manifests remain under `experiments/middle-coherent-incidence-nuc-vN`.
V3 has one unused `DecidableEq I` section-variable linter warning. Both
989-entry provenance checks passed and `PROVENANCE_UNCHANGED=true`.
All final audits use only `propext`, `Classical.choice`, and `Quot.sound`.
There is no `sorryAx` in the successful log. The compiler slot was explicitly
released after terminal postflight; all triplets and the green olean were
then copied locally and their hashes verified.

| Green artifact | SHA-256 |
| --- | --- |
| Source / v3 exact snapshot | `bbbfa5c901324aa90d2c1de46ce1b6401c38038921c0a114c238619ef7da0115` |
| Olean | `b1d817f34b6092daec64da8dd05adc9686a4d770453c40f73278d78353a5aafa` |
| Manifest | `ec853c0527e2e268918c2881443922d40fc9f65522cdf57bd45d8e7ffafa5a7e` |
| Log | `ad06232f7dfaa739917e80525351a8f89f97ed7ee642ce033491b692bb1ac473` |
| Runner | `5780e61b4d286905ab912bb6ab8e103a20908f78c11bea415db40a5fad110e52` |
