# Selected copy endpoints and patterns to weighted rows

Continuation from `9254b2416c3f8c3c488d0475a00d812fee836e00` on the existing
research branch. No Rust, production default, transcript, proof-byte,
verifier-operation or main-branch change.

## New deterministic bridge

The earlier weighted-row theorem required callers to supply
`inactiveWeights`: every row outside the selected active mask had zero
producer and consumer weights. This continuation constructs the row family
from the **actual 136 compiled links and 14 tuple patterns**, checks their
endpoint rows against that mask, and derives the condition. It does not
repeat the generic field-balance proof.

The target `source_layout_balance_zero` retains the actual prerequisites:

- Every selected Boolean copy-row residual is zero.
- The total helper sum and the inactive helper sum are zero.
- All four slot denominators at every active row are nonzero, including
  slots belonging to public zero-weight links.

It then concludes that the entire constructed row family's weighted rational
balance is zero. No inactive-weight assumption remains in this endpoint.
No valid witness, decoder success, honestly generated trace, or verifier
acceptance premise supplies the removed condition.

Both new files passed their first focused NUC check. The eight printed axiom
audits contain only standard axioms; the two finite layout certificates use
only `propext`. No failed check or unchanged rerun was needed.

## Exact source data and model

Source is
`crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal_constants.rs`,
with the evaluator in the adjacent `pair_forest_copy_terminal.rs`. The new
`SelectedCopyLayout.lean` contains every producer/consumer row, slot and
pattern in the same order as `COPY_LINKS`. It uses the already checked tag
and public-weight schedule in `SelectedWeightedCopyRows`; no old 183-link
atomic or 78/75-link native registry is substituted.

Each source pattern has a contiguous active prefix. Its exact compact
descriptor is `(width, first_column, final_active_limb_offset)`:

```
0:(16,0,0)  1:(8,0,0)   2:(6,2,0)  3:(6,0,0)
4:(2,0,0)   5:(2,6,0)   6:(1,0,0)  7:(1,10,0)
8:(1,1,0)   9:(1,2,0)  10:(8,8,1051521018)
11:(8,2,0) 12:(8,1,0)  13:(8,8,0)
```

The generation preflight compared this description against every one of the
224 source pattern cells, including unused zero cells, and checked every
endpoint's bounds. In particular, pattern 10 retains its nonzero offset;
it is not incorrectly identified with pattern 13. The pattern-range theorem
and its dependent read bound ensure every live read uses column 0 through 15.

The static endpoint certificate checks 272 small endpoint/mask occurrences,
not field values or a circle recurrence. It proves that both endpoints of
every link occur in the actual 214-row mask already defined in
`SelectedWeightedCopyRows`. Only this finite public certificate uses kernel
computation; the subsequent table reasoning is symbolic over an arbitrary
field.

`SelectedCopyLayoutRows.sourceRows` models the compiled fixed-slot path:

```
slot_value = sum of compressed tagged tuples placed at (row,slot)
slot_weight = sum of public weights placed at (row,slot)
compressed = tag + sum_{j=0}^{15} lambda^(j+1) * pattern_limb[j]
```

The value sum is independent of the public weight. This preserves the source
behavior at zero-weight links and hence the earlier zero-weight-pole
regression. The new theorem also derives that all slot values vanish
*outside the whole active mask*. It does not claim that a zero-weight slot
inside the active mask has value zero.

The independent host builder searches for a free slot using zero weights.
This model instead uses the selected generated fixed slots. Equality of
those two implementations' relevant rational behavior is not assumed here.
Likewise, the finite-sum field model of additive endpoint accumulation is
not a translation of the optimized SBF loop, pattern-window kernel, or
mutable field arithmetic. Those source refinements remain explicit.

## What changed in the dependency map

| Interface | Status in this continuation |
|---|---|
| Literal 136 producer/consumer endpoint placements | New source-shaped definitions, with source metadata preflight |
| Literal 14 patterns including all offsets | New equivalent compact definitions; all 224 cells checked by metadata preflight |
| Every endpoint row lies inside the selected mask | New kernel-checked static certificate |
| Every live pattern read is within 16 columns | New kernel-checked range/read proof |
| Constructed row weights vanish outside the mask | New kernel-checked symbolic theorem; no caller premise |
| Constructed row values vanish outside the mask | New kernel-checked symbolic theorem |
| Exact constructed row family consumes old global balance theorem | New kernel-checked dependent endpoint |
| Source selectors/optimized accumulation evaluate to these Boolean sums | Separate source-shaped loop/kernel refinement; not inferred from matching metadata |
| Row rational sum equals active-link compressed multiset balance | Next deterministic step, including endpoint-slot uniqueness and weight-zero handling |
| Chi/lambda collision exclusion yields selected weighted aliases | Still required after the selected link-sum bridge |
| Acceptance enforces local residuals and both helper sums | Separate causal image/row/semantic source theorem |
| C1 candidate list completeness and checked payment extraction | Separate obligations; no family member or witness is assumed here |

This removes a real public-layout premise from the new endpoint but does
not derive all 2,176 weighted alias residuals or literal payment acceptance.
The alias endpoint for an inactive link remains
`weight*(producer_limb-consumer_limb)=0`, not unconditional tuple equality.

For later probability composition, the candidate C1 table must come from the
appropriate pre-lambda family; public variant/append index must be bound at
their actual prefix, and helper responses may depend on prior challenges.
The deterministic theorem quantifies over those inputs without proving their
causal fixing or fresh-challenge law. There is no new pole, copy, semantic or
authentication probability in this report.

## Focused evidence and limits

The coordinator's fresh NUC overlay was
`/home/dombarker/project-offloads/aspis-component-cover.ZIUqzo`. The existing
green weighted-copy leaves and pinned native packages were reused. The
smallest layout certificate was compiled first, then its dependent row
bridge, with no concurrent build. Both ran through
`run_component_cover_nuc.sh` with Lean 4.32.0 `-j1 -M9500`, MemoryHigh 8 GiB,
MemoryMax 10 GiB, MemorySwapMax 0 and CPU quota 200%. Actual usage stayed
below two million KiB RSS.

| Focused target | Exit | Wall | Peak RSS (KiB) | Swap | Axiom audit |
|---|---:|---:|---:|---:|---|
| `SelectedCopyLayout`, v1 | 0 | 2.36 s | 1,913,972 | 0 | 2, `propext` only |
| `SelectedCopyLayoutRows`, v1 | 0 | 0.87 s | 1,731,268 | 0 | 6, standard-only |

The log and corresponding per-run `-manifest.json` files are retained under
`experiments/`, with tags `selected-copy-layout-nuc-v1` and
`selected-copy-layout-rows-nuc-v1`. Both green oleans are also local. Each
successful run verified unchanged overlay provenance before and after Lean.
Native packages are a pinned-revision cache boundary, not a claimed replay
of their compilation. The borrowed source pin remains
`26a9cd4718aae9f9de7ef1c3394fb74a229085d5`.

| Artifact | SHA-256 |
|---|---|
| Layout source | `6cd33c59ff9507c48682319d31dff95c91a1862f434f21fb9e63b177acade362` |
| Layout olean | `5397ed9ebbdcc1c4baeae33a2c871f8d51196167f45731ba99c4a90b199f5f71` |
| Layout log | `1a249bfc0a13289f7fdc413dcb052ac7955b00283b23347d7e5dbf9ca534fd9b` |
| Row source | `e0c5ee9464e75d8c642299353d8f5922d5fb29de9bd4248e2213d2a7c8e30a5b` |
| Row olean | `ebedf6159f4961be13c668d6a21a95eb445c1c820815cca6d4314d345276fb75` |
| Row log | `a44896fabf79125ccb3a6dfb1b3087f8779187523112a01428d77318ede94c75` |
| Pinned generated constants | `cfce7ec499d3cfd54cf91eb88675e45d89ada5ce073fe00c78be5211204fbc50` |

An independent read-only comparison against `git show` at the parent pin
also matched all 272 endpoint triples (816 numeric fields), all 136 tag
indices, and all 224 pattern cells (672 kind/column/offset fields). It parsed
the Lean `link` entries and the fourteen `(width,start,lastOffset)` literals;
each pattern cell reconstructed exactly as described above. This metadata
check is not a source-loop translation or a field/probability experiment.

Actual focused commands were:

```sh
ssh dombarker@nuc.local 'bash /home/dombarker/project-offloads/aspis-component-cover.ZIUqzo/run_component_cover_nuc.sh /home/dombarker/project-offloads/aspis-component-cover.ZIUqzo SelectedCopyLayout selected-copy-layout-nuc-v1'
ssh dombarker@nuc.local 'bash /home/dombarker/project-offloads/aspis-component-cover.ZIUqzo/run_component_cover_nuc.sh /home/dombarker/project-offloads/aspis-component-cover.ZIUqzo SelectedCopyLayoutRows selected-copy-layout-rows-nuc-v1'
```

No laptop compiler, unchanged replay, field enumeration, source Rust rebuild,
SBF build or CU measurement ran. Future justified reruns need fresh log tags;
these green sources and outputs remain frozen.

The 40,282-byte maximum body, full-view privacy and resource-bounded FS
requirements are unchanged. The decisive next deterministic step is
endpoint-slot uniqueness plus the row-to-active-link rational sum identity,
which makes this concrete row balance usable by the selected family-wise
copy argument.
