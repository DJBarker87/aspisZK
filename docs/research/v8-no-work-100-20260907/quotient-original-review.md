# Image-valid quotient to the actual original code

Research source pin: `51b78cbf7fadee4ec70328c86add7678a43f21da`.
Borrowed formal source/cache pin: `26a9cd4718aae9f9de7ef1c3394fb74a229085d5`,
the same cache already recorded by the selected encoder/oracle and
pre-anchor results. Imported source and olean hashes are checked before and
after the focused runs; advancing main is not used as an implicit pin.
No Rust, transcript, proof-body, query-count or production change is made.
This is a deterministic coefficient/domain bridge, not a new probability
estimate or payment-knowledge theorem.

## Concrete construction

For the actual OOD data `d` and natural1024 quotient coefficients Q, define

```
U = reconstruction(d.a,d.b,d.c)(Q) + d.interpolant.
```

`reconstruction` is the retained TOTAL natural-basis projection of chord
multiplication, not monomial truncation. The interpolant is the literal
two-entry source vector, using x when the OOD x-coordinates differ and y
otherwise. The checked slope-inverse boundary proves the chord nondegenerate.
Neither OOD answer correctness nor received-word polynomiality is assumed.

With the literal image conditions `Q[1023]=0` and
`b*Q[1022]-c*Q[1021]=0`, the bridge proves at each exact stored log20 index

```
exactInitialEncoder(U)[i]
  = L[i] * exactInitialEncoder(Q)[i] + exactInitialEncoder(I)[i].
```

The domain points and encoder are the V7-consumed bit-reversed, fibre-major
mathematical evaluator. The circle equation comes from each stored point's
proved circle-group membership. No basis/encoder equality is supplied as a
new correspondence premise. `original_eq_rows` identifies U with the same
concrete reconstruction and interpolant used by the repaired ordinary rows.

## Poles are counted, not silently excluded

The virtual received quotient is totalized:

```
R[i] = (received[i] - exactInitialEncoder(I)[i]) / L[i].
```

Field division returns zero at a zero denominator. The verifier's queried
checks do not themselves prove that L is nonzero at every unqueried position.
Consequently the bridge keeps a deterministic pole set.
The source still rejects a queried zero denominator. The totalized ideal
word is therefore an over-approximation at that abort boundary, not a claim
that the source accepts its zero values. A full source/game adapter must
preserve the abort.

For the retained stereographic parameter `t=y/(1+x)`, a chord zero is a root of

```
(a+b) + 2*c*t + (a-b)*t^2.
```

The checked chord is nondegenerate, making this quadratic nonzero. Existing
V7-consumed exact-domain facts prove the stored points avoid the west pole
and their embedded stereographic parameters are distinct. Thus there are at
most **two pole symbols**, hence at most **two pole fibres**. This reuses the
actual domain geometry, not the generic degree1024 overlap bound.

The resulting deterministic inclusion is

```
fibreBad(Encode(U), received)
  ⊆ fibreBad(Encode(Q), R) ∪ poleFibres.
```

Outside poles, quotient/original agreement is equivalent, with the literal
subtraction/division signs. No probabilistic conditioning or pole-failure
probability is introduced.

Using the analysis-only folded threshold B=2324, the existing 4B geometric
quotient bound transfers to at most `4*2324+2 = 9298` original bad fibres.
That fits inside the already proved 9301-radius near-gamma regime. B is an
analysis cutoff, not a protocol or proof-size parameter change.

## Reused facts and new interfaces

| Interface | Evidence consumed | New work |
|---|---|---|
| Total chord reconstruction | `InterleavedChordRows.message_circle_eval` | Add the actual OOD interpolant linearly; identify the literal row-constructor message |
| Actual stored domain | V7-consumed `exactInitialEncoderCircleRealization` and log20 point facts | Instantiate circle membership, west-pole exclusion and parameter injectivity at each actual index |
| Pole bound | Generic circle `stereo_identities`, finite polynomial root count | Derive the nonzero quadratic chord numerator and count at most two stored poles |
| Whole-fibre transfer | Retained `quotient_eq_iff_reconstructed` and source `childIndex`/`parentIndex` | Prove agreement equivalence away from poles, inclusion of bad-fibre sets, and the literal 9298 ceiling |

No V7 q16 query law, work multiplier, operational resource cap or assumed
Rust/evaluator equality is used as a hypothesis of these new results. V7
resource modules occur transitively in the borrowed import closure; that
does not promote their protocol-specific claims to this V8 argument.

## Scope and next interface

The original word is `exactInitialEncoder(U)` by construction, but this alone
does not establish component-wise original-code membership, honest masking,
correct individual point claims or a valid payment witness. The raw received
word must next be the SAME scalar-power gamma batch of the fixed C1/C2
words. C1's near-gamma mathematical bridge supplies that representation and
the literal own-support projection; source challenge timing, authenticated
access, full-view ZK and the FS lift remain distinct obligations.

## Focused evidence

Both leaves are kernel-checked. The [core v2 log](experiments/quotient-original-core-v2.log)
records 9.78 seconds, 5,640,962,048 bytes peak RSS, zero swaps and exit 0.
The [selected v6 log](experiments/selected-quotient-original-v6.log) records
18.67 seconds, 5,758,877,696 bytes peak RSS, zero swaps and exit 0. All five
core and nine selected printed declarations use only `propext`,
`Classical.choice` and `Quot.sound`; neither source contains `sorry` or a
new axiom. Both successful runs finish with unchanged source/cache provenance.
Exact source/olean hashes and status are recorded in
[quotient-original-evidence.json](quotient-original-evidence.json).

Core v1 failed locally while broad simplification tried to recover three
polynomial coefficients. It was replaced by the existing symbolic
`monomialPolynomial_coeff` theorem, without increasing a resource limit.
Selected v1/v2 stopped in provenance preflight, before Lean: their runner
incorrectly demanded equality between research-era and the already borrowed
formal source. The corrected runner declares and verifies both pins above;
it does not overwrite the cache or import a new V7 resource claim.
Selected v3 found two local unfolding/namespace issues and an eager `change`
normalization in the pole proof. The fix uses explicit map naming and a
symbolic denominator rewrite. V4 was deliberately terminated after a
compile-slot handoff race, to preserve serialized builds; it is not retained
as successful evidence or a memory-failure result.
V5 isolated the remaining ring-hom division lemma: `map_div₀`, not the
group-only `map_div`. V6 makes that one-line correction without a cap change.

Commands, from this research directory with fresh log filenames:

```
bash experiments/run_quotient_original.sh QuotientOriginalCore experiments/quotient-original-core-v2.log
bash experiments/run_quotient_original.sh SelectedQuotientOriginal experiments/selected-quotient-original-v6.log
```

The runner pins the imported source closure, records source/olean hashes
before and after each focused check, uses Lean `-M7000` plus an independent
aggregate 7 GiB guard, and records wall time, peak RSS, swaps, exit and axiom
audits. No unchanged large proof or SBF build is scheduled.

The proof-body model remains `697*16 + 52 + 24 + 22*621 + 2*296*26 = 40282`
bytes. These are proof/source artifacts only: no verifier operation, transcript
message or public disclosure was added. No host timing, proving time, SBF CU
or complete-transaction measurement is inferred from Lean resource usage.
