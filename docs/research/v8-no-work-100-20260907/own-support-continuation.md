# Represented tuples with insufficient own support

Continuation parent: `ed41b2537e7dad15ce8055d9e5524e337ee8b9a4`, on
`research/v8-no-work-100-20260907`. All Lean checks run on the NUC, not the
laptop. Production and concurrent main work are untouched.

Status: the restricted source/count integration is kernel-checked through
`SelectedOwnSupportGame.literal_family_count`, including the actual fixed
family's cardinality bound. Nine new leaves contribute 57 standard-only
axiom audits; the separately exported old dependency contributes 17 reused
audits. See the [evidence census](own-support-build-evidence.md). The
[rational ledger](own-support-ledger.json) is a restricted class calculation,
not a completed V8 security budget.

## What this closes mathematically

The previous linear-factor classification returned a fixed family of at
most111 component tuples. It did not establish that the tuple representing
an adaptive quotient has enough **componentwise own support** to enter the
early-C1 family. Merely finding a representing tuple was not that bridge.

The new joint argument covers precisely the represented, literal-covered,
image-valid, true-final branch whose tuple has fewer than38,228 jointly
matching original symbols. It retains arbitrary received words and adaptive
selection of the quotient/final. It neither supposes that all accepted
branches have this form nor suppresses the higher-Y factor alternative.

For a fixed tuple p, write S for its own symbol support. At symbol i define

`r_i(X) = sum(lane=0..28) X^lane * (received_lane(i)-encode(p_lane)(i))`.

This polynomial is zero exactly on S and has degree at most28. Let E be
the union of its roots outside S. Then

`|E| <= 28*(1048576-|S|) <= 29360128`.

A literal covered quotient has at least9,558 full matching fibres.
The existing checked chord/image reconstruction loses at most two symbols,
leaving at least38,230 original batch matches. If its reconstructed message
is `batch_gamma(p)` but |S|<38,228, at least one of these matches is outside
S. Thus gamma belongs to the **fixed**, pre-gamma set E. This is a derived
exception implication, not assumed provider membership.

This exception bound by itself is not the answer: its coarse probability
is too large. We use it jointly with queries.

Let C be the fibres wholly inside S, J=|C|. The source's injective four-slot
map gives 4J<=|S|, hence J<=9,556. Split the fresh query schedules:

- All queries in C: charge the gamma event E as well as the common-query
  probability. The contribution is `beta(J)*|E|/|G|`, not `beta(J)`.
- Some query outside C: select one bad slot from the schedule before gamma
  and alpha. Its component residual has at most28 gamma roots; otherwise
  its divided fold is a nonzero degree-at-most3 alpha polynomial. The old
  fixed-target argument applies after the actual source residual is
  rewritten, without freezing the adaptive Q earlier.

For each tuple, the exact integer upper bound on the finite-product count is

```
choose(J,q)*|E|*|A|
  + (choose(T,q)-choose(J,q))*(28*|A|+(|G|-28)*3).
```

The fixed-family union applies to these **joint charged events**, including
the tiny charged common term. It does not pay111 times a bare q22 tail.
Under the explicit ideal law |G|=k-1, |A|=k and uniform distinct22-subsets,
the safe coarse111-member bound is

```
111 * [ choose(9556,22)/choose(262144,22) * 29360128/(k-1)
        + 28/(k-1) + (1-28/(k-1))*3/k ],
k=(2^31-1)^4.
```

Its exact rational display is **112.2513878206 bits**. The script also
checks the independent integer-numerator normalization; the strict
`2^-113 < bound < 2^-112` assertion uses rationals, not decimal logs.
Nothing here establishes a universal probability against offline search.

## Checked dependency map

| New leaf or endpoint | What its checked conclusion supplies |
|---|---|
| `OwnSymbolCollision` and `OwnFibreGeometry` | Fixed gamma exception from excess symbol agreement; injective four-slot own-support cap |
| `TupleQueryTransportCore` and `TupleQuerySymbols` | Literal encoder batching, chord residual and nonzero cubic, retaining arbitrary received words |
| `TupleQueryTransport.query_zero_iff` | Actual selected query-zero predicate equals the cubic-zero predicate under the stated image/representation/true-final premises |
| `SelectedOwnSymbol.covered_forces_exception` | Those actual selected premises force the fixed gamma exception when own support is insufficient |
| `InsufficientOwnSupport` and `InsufficientOwnSupportFamily` | Pole-guarded joint count and adaptive selection from a fixed family |
| `SelectedOwnSupportGame.literal_family_count` | Composes the source-shaped interfaces with the actual pre-OOD family; derives its size at most 111 |
| `SelectedOwnSymbol.own_supported_early_member` | The complementary supported tuple projects into the genuinely early-C1 mathematical family |

Every row is kernel-checked. The predicates and restrictions in the rows
are part of their scope, not acceptance-to-recovery facts assumed to have
been proved elsewhere. Source details are in
[the transport review](tuple-query-transport-review.md) and
[the joint count review](insufficient-own-support-review.md).

## Actual source-map connection

The tuple's expected word uses `exactInitialEncoder`, and its received
word uses the literal26-C1-plus3-C2 `received29` assembly. Existing V7 encoder
linearity yields the scalar-power batch identity. On a legal source slot,
checked image reconstruction gives

`virtual_gamma - encode(Q) = r_i(gamma)/L(i)`.

The denominator is fixed before gamma: `atGamma` changes the interpolant,
not the chord. The generic four-slot algebra yields the signed identity

`actual final-minus-received query residual = -fold(r/L)(alpha)`.

The negative sign follows the source's residual convention. The concrete
selected adapter proves exactly what acceptance needs: actual fold
equality, and actual ordered query residual zero, if and only if the
constructed fold polynomial evaluates to zero. Full concrete negative-value
conversion attempts failed elaboration and are not claimed as checked
endpoints. The generic signed identity remains proved. No correspondence
equality is supplied by the caller: the quotient disappears using its
actual reconstruction identity and true-final equality, even when selected
after alpha. The checked concrete adapter uses the actual canonical
twiddles and their existing inverse equations, avoiding alternate instance
normalizations. All retained modules remain at elaboration depth200.

The supported event excludes each schedule with a queried pole; this is
not a newly proved Rust rejection law. We do not assume that the chord is
nonzero everywhere, delete pole fibres, or renormalize the query
distribution. A schedule containing a queried zero denominator has zero
mass in this supported pointwise event. The finite count retains the whole
262,144-fibre query universe.

These are source-shaped mathematical maps and counts, **not** a translated
Rust/parser/authentication/rewinding theorem. Scalar acceptance with failed
pointwise checks remains in the separately charged shifted-rho and later
relation-repair events. The q-subset identity is used only for the
order-insensitive pointwise event, not for the later scalar continuation.

## Remaining accepted-extraction accounting

The objective remains `Pr[A and not X]`, where X is a bounded extractor
returning a witness accepted by the payment/context/settlement predicate.
The following is the current obligation map, not a proved total verifier
partition. Assign precedence when composing the actual experiment.

| Class or interface | Current treatment |
|---|---|
| Source/authentication mismatch, abort/fuel, missing responses, cached/advance mismatch | Still visible; no invented probabilities |
| Scalar acceptance with failed pointwise checks; false/off-final and image/row repair events | Existing causal game bounds, compose once under actual laws |
| Outside-literal-family or unrepresented-final mass | Retained in prior off-family/false-final obligations; not erased by this event definition |
| Good covered selected quotient, retained factor exceptional OOD/gamma case | Previous classification retained; sampler/source composition still required |
| Retained factor with Y-degree>=2 | Still unresolved; no assumption of a linear factor |
| Represented tuple, fewer than38,228 own symbols, true final and pointwise success | New joint bound above |
| Represented tuple, at least38,228 own symbols | Actual projection belongs to fixed early-C1 family; membership is not a witness |
| Early-C1 member missing exact semantic/copy/path/public constraints | Earlier conditional copy theorem helps; acceptance-to-constraints remains |
| Mathematical tuple/early family to bounded authenticated recovery and checked payment | Not inferred from noncomputable existence |

An execution can have more than one representing tuple, including tuples
on different sides of the own-support cutoff. The insufficient event is an
existential overcount, not an assertion that extraction fails whenever one
such tuple exists. A total partition needs an explicit selector or event
precedence; the finite-family union remains valid without disjointness.
One possible accounting order is source/replay, scalar/off-final, outside
literal family, bad image/row, OOD/sparse factor, higher-Y, insufficient own
support, then own-supported payment/recovery failures. Restricting the new
event to the complement of preceding events uses inclusion under the
original law; it does not license conditioning away those events and
assuming the challenge distribution is unchanged.

C1 stays fixed before lambda/chi. C2 may depend on them. The111-tuple
family depends on both commitments and is fixed before gamma; it cannot be
moved before lambda. On the supported complement, the separate early-C1
family is defined from C1 alone. The exact projection theorem gives
membership in that family, allowing its genuinely early timing to be used
where the remaining constraint premises are established.

Both component-OOD vectors retain their sequential absorption.
The existing degree2 helper curve and degree28 component-claim error remain
in the inherited factor/claim construction; neither is replaced by an
independent degree-zero helper assumption.
Ordinary claims and chord precede kappa/tau; corrected row powers are1,kappa,kappa²,
kappa³. Tau carries the image checks before response0; response0 precedes
alpha0, the final may follow alpha0, queries precede rho, and later compact
responses may depend on all earlier challenges. No step earns work bits.

The old local104.366-bit reduction ceiling is not recomputed or relabelled
global security. Its event composition with the new class, higher-Y mass,
copy/semantic/source/authentication and extraction obligations remains
explicitly incomplete. The machine ledger leaves global bound and global
remaining allowance null. Full-view ZK and resource-bounded Fiat–Shamir are
separate gates. No quantum claim is made.

## Regressions and falsification

Original J=9557 and paired J=9556 root products still refute same-support
recovery; this argument uses the tuple's own support instead. High-J=252843
remains own-supported; extra batch-zero fibres need not match componentwise.
For the original zero reference tuple, 4*9557=38,228 is exactly the
own-supported boundary, not part of the new insufficient event. The paired
zero reference has only38,224 common symbols, but its known OOD
incompatibility is not erased: the theorem requires the actual
reconstruction to be represented, or leaves that branch in the remaining
classification. Neither example becomes a payment witness by naming zero.
T512 and the zero-fold/nonzero-image kernel still require the carried image
gate. The unshifted row cancellation and late-inactive timing falsifier stay
rejected; shifted degree-q batching and legitimate later repair collisions
remain charged. Radius9302 still need not be extraction failure. None of
these unchanged fixtures was rerun merely to add a test count.

The new tiny exact F7 control preserves three falsifiers of tempting
shortcuts: dropping the gamma charge, choosing the exception set after
gamma, and treating division by zero as a permitted opening. Each violates
the proposed count in its restricted model. See
[the exact controls and scope](insufficient-own-support-review.md).
They are not an exhaustive search of full causal verifier strategies.

## Costs, decision and reproduction

The body stays **40,282 bytes**:
`697*16+52+24+22*621+2*296*26`. No verifier code, transcript, public messages,
proof values or operations change in this continuation. There are no new
CU, SBF, proving-time, extractor-time or RAM measurements for those paths.
The NUC memory figures describe Lean checks only. Previous optimisation
evidence is neither regressed nor upgraded by this mathematical work.

The q22 direction remains worth pursuing: the linear represented branch
now has a checked quantitative reduction to the early-C1 own-support split,
without a 111-fold bare query loss, extra bytes or field changes. It is not
yet production-certified. The next decisive experiment is a symbolic
classification or falsifier for **retained higher-Y-degree factors under
the two actual sequential OOD identities and the degree2 helper curve**.
That is the remaining factor-coverage alternative; another own-support
radius sweep would not address it.

Focused NUC runner (one target at a time, fresh tag):

```sh
bash /home/dombarker/project-offloads/aspis-own-support.f6NQzi/run_own_support_nuc.sh \
  /home/dombarker/project-offloads/aspis-own-support.f6NQzi TARGET FRESH-TAG
```

The runner records the exact pinned `lake env`/Lean leaf command,
source/olean hashes, capped cgroup, wall/RSS/swap and axioms. Reuse green
dependencies; do not replay the package. Laptop-only metadata checks:

```sh
python3 docs/research/v8-no-work-100-20260907/experiments/own_support_ledger.py --check-recorded
python3 docs/research/v8-no-work-100-20260907/experiments/audit_own_support_evidence.py --check-recorded
```

The old `FixedTargetQuerySupport` proof lacked an exported compatible
olean. One authorized export of its byte-identical source restored this
dependency; its17 audit declarations are reused work, not new mathematics.
All failed attempts are retained separately from green evidence.

The final selected leaf completed in 3.14 seconds, with 6,862,244 KiB peak
RSS and zero swaps, under the serial 10 GiB memory/2-CPU scope. This is
compiler resource evidence, not proof-generation or verifier performance.
No unchanged full Lean manifest, SBF build or deployment was run. The
publication commit contains only this continuation's research artifacts;
concurrent main changes are outside its scope.
