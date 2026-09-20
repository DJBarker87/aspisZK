# R17 source-shaped algebra bridge

Date: 2026-09-20. Base revision
`0bcca87a835fcb050328c58deb18a440b26d237e`, plus this proof changeset.
No Rust or protocol source changed. These are universal algebraic results,
not a complete Rust semantics, commitment extraction, or privacy proof.

## Reverse mask loop

`lean/AspisV8R17/SourceMaskLoop.lean` models the source's accumulator
`(out, scale)`, initially `(0,1)`, processing round contributions in reverse
order with `(out + contribution*scale, scale*half)`, then adding
`initial*scale`. It proves equality to a literal reverse-list `foldl`, not
just a recurrence asserted to resemble the loop.

For contributions given by the existing zero-boundary `roundEval`, the
accumulator equals `structuredMask` for every field with nonzero 2 and
every number of rounds. Therefore its full Boolean-cube sum is the initial
coordinate, and its next suffix sum is exactly `semanticRound`. This
connects the reverse source evaluation order to the previously proved
forward recurrence, without enumerating 1024 concrete Boolean inputs.

The source anchor is `tools/r17_structured_g.rs`, SHA-256
`147be74e8651e05aa4680dbb412252751e8f21f5a6ad8a4de939d0f01bfb52c6`.
Still required: the Rust array slicing/index order and `zero_boundary`
power loop refine the list of `roundEval` contributions, and QM31 operations
refine the abstract field. The theorem does not assume or prove those facts.

## Arbitrary-input channel errors

`lean/AspisV8R17/ChannelResidual.lean` proves the projected-claim identity
`u(all-g)+v(g) = u(all)+(v(g)-u(g))`, including its pullback through the
common additive transport. Here `g` represents the already gamma^27-scaled
G column and `all-g` the complementary batch.

More importantly, it retains malformed-input errors. For arbitrary
committed vectors, interpolants, submitted quotients and a claimed scalar,
the verifier's claimed-minus-quotient discrepancy equals:

1. the claimed scalar minus the true projected functional value;
2. the ordinary functional of the ordinary column/interpolant/quotient residual;
3. the G functional of the G column/interpolant/quotient residual.

There is **no premise that submitted quotients or claims are correct**.
Nor does the theorem infer that the three errors vanish individually when
their sum vanishes. That inference requires the actual independent checks,
extraction and batching bad-event accounting. This preserves, rather than
silently erases, the carried/ordinary error in the degree bounds.

Source anchor: `tools/r17_host_relation.rs`, SHA-256
`4778e671d2a41975d47961dcd699ec772ca9183321e496d37810180f15c63bfb`.
Its parser, packed G projection, gamma powers, functional construction and
opening authentication still need the exact source refinement/extraction
argument. The additive maps in this algebra are not that argument.

## Focused compilation and axioms

Cached workspace `/Users/dominic/ZK/AspisFormal`; each command uses
`lake env`, `lean -j1 -M1800 -R <pack>/lean`, with the existing
`target/r17-lean` and `target/r16-lean` prepended to `LEAN_PATH`. Outputs
are the matching `.olean` files in `target/r17-lean/AspisV8R17`.
No package-wide replay or unchanged Rust suite was run.

| Target | Exit | Wall seconds | Peak RSS bytes | Swaps |
| --- | ---: | ---: | ---: | ---: |
| `ChannelResidual.lean` | 0 | 8.84 | 1353269248 | 0 |
| `SourceMaskLoop.lean`, initial bridge | 0 | 6.91 | 1686519808 | 0 |
| `SourceMaskLoop.lean`, added reverse-fold and suffix endpoints | 0 | 2.49 | 1695170560 | 0 |

All four channel endpoints and all six audited mask endpoints report only
subsets of `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, new
axiom, distribution assumption or hiding assumption is added.
Logs: `/tmp/aspis-r15-host.drHYn9/r17-channel-residual-lean.log`,
`r17-source-mask-loop-lean.log`, `r17-source-mask-loop-final-lean.log`.

## Remaining boundary

The loop-order and arbitrary-input residual algebra are now proved. The
first remaining source bridge is the concrete field/index/packed-column
refinement just identified, composed with the transported chord weights.
The joint H1/G causal posterior, adaptive exceptional-event bounds,
commitment/shared-oracle/seed expansion, and failure/retry/publication laws
remain necessary. Neither these algebraic identities nor the prior host
acceptance tests establish full privacy or malicious-prover soundness.
