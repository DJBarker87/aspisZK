# Early C1 family to selected copy collisions

Continuation from `2f6d82fef294410367aa1781fb924af7c38deab9` on the existing
research branch. This is a proof-only connection to the selected 136-link
copy calculation; no production, Rust, transcript or proof-byte changes.

Both new leaves are kernel-checked. The selected endpoint now couples the
actual ≤100 pre-lambda family to the literal copy collision witnesses,
including arbitrary later member/helper selection. It does not establish
that every accepting execution supplies an eligible family member or the
copy-row/helper premises.

## Exact covered event

The previous selected-copy theorem applied to one supplied coefficient
table. This continuation fixes the table-selection timing by consuming
`EarlyC1Family.family c1`, defined from the committed received C1 alone.
It contains every 26-column original-code tuple whose **own** joint support
has at least 38,228 symbols, and has at most 100 members. This is the
unfiltered family, not the optional dominant candidate or a Cartesian
product of per-column lists.

For each member p, `memberTable p row column` transposes the first sixteen
message columns. The selected registry's existing `pattern_read_in_range`
proves every live tuple read lies in those columns. The new interface keeps
the public last-limb offsets and proves the literal late 26+3 projection
reads this same table. Unused columns of the total copy-table interface are
zero-filled; this does not impose zero constraints on the remaining ten C1
columns or on random mask cells.

`actual_late_covered` consumes the existing
`actual_late_projection_member`: a late width-29 tuple with its own
38,228-symbol support supplies membership in the early family. No equality
to a dominant tuple, whole gamma-batch support, decoder membership or honest
trace is assumed. Proof acceptance supplying that support is still open.

For each member p define the actual previous witnesses:

- L_p: selected lambda collision polynomial, fixed from p and the public
  active layout before lambda; degree at most 16n.
- C_{p,lambda}: selected chi Wronskian, fixed from the same p/layout and
  lambda before chi; when nonzero, degree at most 2n−1.

Here n is the actual active-link count and n≤136. The latter subtraction
also handles n=0: no nonzero Wronskian exists in that case. No old 183-link
registry or historical 396430 inventory is used.

For arbitrary fixed finite challenge domains Lambda and Chi, form the union
of each family's nonzero-polynomial root sets. The proved exact counts
are

```
|lambdaCollisions| <= 100 * 16n
for every lambda: |chiCollisions(lambda)| <= 100 * (2n-1).
```

`coveredFailures` is the finite set of pairs (lambda,chi) for which there
exists a member of the early family and a helper satisfying all the literal
selected local-row, total-helper, inactive-helper and four-slot non-pole
conditions, but that member's weighted aliases fail. The selected member
and helper may be chosen after both challenges and later observations.
The witnesses come from the earlier family, not from freezing that choice
retroactively.

The endpoint places every such pair in one sequential union and
bounds its cardinality by

```
100*(16n)*|Chi| + |Lambda|*100*(2n-1)
  <= 217600*|Chi| + 27100*|Lambda|.
```

This is a union upper bound, not a claim that the two collision classes are
disjoint. Every source pole remains an explicit prerequisite, including
zero-weight or empty slots on active rows. The source values are not
multiplied away when a public weight is zero.

## Causality and global limits

The domains, received C1 and independently bound public variant/append
context must be fixed at the appropriate early prefix. For a uniform pair
draw from Lambda × Chi, the finite count would yield
`100*16n/|Lambda| + 100*(2n-1)/|Chi|` when both domains are nonempty.
This is only the stated ideal-law interpretation, not a newly proved SHA,
bounded sampler, Fiat–Shamir or source acceptance theorem.

The chosen table may depend on C2/lambda/chi only by choosing a member of
the already fixed family. A table constructed after C2 with no established
membership is not covered. The following mass remains separate:

| Execution branch | Treatment |
|---|---|
| In-family, source premises true, aliases false | Covered by the new collision union |
| In-family, aliases true | Copy success only; semantic/decoder/payment checks still required |
| Outside the early family or insufficient component own support | No bound supplied here |
| Local/helper identities missing, any required slot pole, or source mismatch | No acceptance-to-premise implication assumed |
| Authentication/replay abort, fuel, missing response, challenge mismatch or provider none | Must be accounted by the actual specified extractor, not identified with this pair event |

The family is mathematical and noncomputable; these proofs do not supply
an efficient list extractor. Existing base-field descent for family members
may be reused under its fixed-base-word premise, but no canonical parser or
payment validation success follows merely from family membership.

No new global charge is booked. The existing local reduction subtotal has
different event premises; composition and all overlaps must be justified
before adding this covered copy term. Full-view privacy and resource-bounded
Fiat–Shamir remain separate. Grinding credit remains zero.

## Source, dependencies and checks

- `EarlyC1CopyCollisionCore.lean`: generic finite polynomial-root unions,
  sequential pair count and arbitrary adaptive member selection; seven
  axiom-audit targets.
- `EarlyC1CopyCollision.lean`: actual first-sixteen-column projection,
  selected QM31 witnesses, ≤100 family specialization, literal late
  own-support projection and covered source-failure count; twelve targets.
- Reused frozen `EarlyC1Family.lean` source SHA-256:
  `5131fa466f65931b8c7a8e783e352903b195d12692e56da67bcdfd3918e1ea3a`;
  cached output `bc30c1e1705fb5310b81de90cac93f54a5a79a598af8d72ccd5e58dd911ad99c`.
- Reused `SelectedCopyAliasQM31.lean` source:
  `a82ddcae4dffa1c8c5e9c3e6a0b65a9a385f1cce425b5eb2d17dde362594e3cb`;
  output `4d2d458e818a81eaba47fa7eb47abf2e22ef7ff18b9074c505eb282528a65e9b`.

Focused run evidence:

| Target / attempt | Exit | Wall | Peak RSS (KiB) | Swaps | Axioms |
|---|---:|---:|---:|---:|---|
| EarlyC1CopyCollisionCore v1 | 0 | 1.03 s | 2,036,044 | 0 | seven standard-only audits |
| EarlyC1CopyCollision v1 | 0 | 3.29 s | 6,714,300 | 0 | twelve standard-only audits |

Core source: `14000d408ef960b9b4590af8f8e84568fe331474d57ace216c68c86cffc3a1e0`.
Core output: `441a6cc5e6209a0ad2f924082d36da5613b90c836bb5b16f4901c4f55b2ad170`.
Selected source: `cc6dbc2f023c67ba2c81dc6722674f696a8d3101edb3400cdc437d2de7684062`.
Selected output: `dd92bdf2df904dbe1ca875f553ab661e978621ba095f2da1b381b58710576c7b`.
Both first attempts passed. Exact source snapshots, logs and per-run
manifests are retained under `experiments/`, using tags
`early-c1-copy-collision-core-nuc-v1` and `early-c1-copy-collision-nuc-v1`.
All nineteen audits use only `propext`, `Classical.choice`, and `Quot.sound`;
neither leaf contains `sorry` or a new axiom.

The NUC scope is `/home/dombarker/project-offloads/aspis-denominator.QNcd5G`,
runner `run_denominator_nuc.sh`, with inherited pinned native packages and
borrowed-source revision `26a9cd4718aae9f9de7ef1c3394fb74a229085d5`.
No cold dependencies or unchanged complete suite replay is requested.

The literal focused commands were:

```sh
bash /home/dombarker/project-offloads/aspis-denominator.QNcd5G/run_denominator_nuc.sh \
  /home/dombarker/project-offloads/aspis-denominator.QNcd5G \
  EarlyC1CopyCollisionCore early-c1-copy-collision-core-nuc-v1
bash /home/dombarker/project-offloads/aspis-denominator.QNcd5G/run_denominator_nuc.sh \
  /home/dombarker/project-offloads/aspis-denominator.QNcd5G \
  EarlyC1CopyCollision early-c1-copy-collision-nuc-v1
```

The runner uses Lean 4.32.0, `-j1 -M9500`, MemoryHigh 8 GiB,
MemoryMax 10 GiB, MemorySwapMax 0, and CPUQuota 200%. Runner SHA-256:
`4a9ee5f24b89642c6a323db95dde0cded2097769c141ed6eb4dcdd16ef8d8935`.
The pinned native-package cache is a provenance boundary, not a new replay
of package compilation. Both runs completed the before/after overlay
checks with unchanged provenance. No concurrent heavy job ran under this
agent's serial grants.

Body remains 40,282 bytes. New verifier operations/messages: none. No SBF,
complete-transaction CU, proving time, replay-extractor cost or public
security claim is measured or changed by this work.
