# Three unknown helpers: full-domain support transfer and the old recovery bound

Research base: `503332fbe747db381fc8ee67c4bbdd3631ec97cf`. This continuation
keeps QM31/q22, the 40,282-byte body and both research relation repairs.
It does not establish a new accepted-extraction probability. No verifier,
production path, proof body or transcript was changed.

## What the older theorem actually supplies

The useful V7 reuse is a concrete code-level theorem, not an automatic V8
acceptance theorem. `V7ExactCorrelatedAgreementInitial.exactV7InitialWidth29CurveDecodable`
discharges the width-29 original-code curve predicate used by
`V6Width29CorrelatedAgreement.width29_bad_response_challenges_card_le`.
The latter counts valid adaptive code candidates whose selected agreement
support cannot be recovered by a component tuple on that same support.
Its valid-response premise includes more than 38,229 original symbols.
The final-code counterpart is
`V7ExactCorrelatedAgreementTerminal.exactV7FinalDegreeThreeCurveDecodable`:
four folding components, degree three, and more than 9,557 final positions.
Neither theorem takes actual repaired V8 verifier acceptance as its premise.

`V6OneFoldCandidateExtraction.accepted_ideal_onefold_supplies_matching_initial_candidate`
requires the query/fold/list failure events to be absent. Its raw-word
consistency support cannot be replaced by V8's quotient/fold support without
a bridge. The mutable main K13 candidate-directed files were not imported
or treated as new proved evidence. The inspected committed source at main
`c7347eefcf767c375040f8f73160995a7886e3ae` retains source-event/collision-map
premises and the V7 q16/resource law, not this V8 q22 execution.

The release initial cap is `336869026605739/(k-1)` and the fold cap is
`9396508281246/k`. The former's expression is linear in curve degree:

```
112 * ((2*112^4/3)/1024 + 1) * degree * 1048576.
```

Changing degree 28 to 2 in that expression would give the integer ceiling
`24062073328982`, about 79.5482 raw bits. Adding the unchanged degree-three
fold cap would give only 79.0726 bits. These are **unproved port/composition
controls**, not a newly applicable bound. The full ordinary/OOD claim
polynomial still has degree at most 28: knowing C1 does not make its false
claim errors disappear.

There is a stronger inner threshold in the checked V7 construction. A
single specified degree-two arithmetic port with `X=114688,Y=112,Z=8363`
has 53,711,659,008 monomials versus 52,615,446,528 constraints and an outer
threshold of 6,237,075,010,843. Even before proving its branch-selection and
exact-message specialization, its gamma-only control is just 81.4960 bits;
adding the existing inner fold threshold gives 81.0283 bits. This was one
dimension/arithmetic check, not a parameter sweep or a security certificate.
The seven inspected theorem/interface files were checked byte-for-byte
against immutable main commit `c7347eefcf767c375040f8f73160995a7886e3ae`;
their source inventory, distinct from the new leaf's borrowed cache pin, is:

| Inspected source | SHA-256 |
|---|---|
| `V6PublishedTheoremInterfaces.lean` | `a0343ca7347a3460a55b1cbf0bc84ab88d73254d5cdcb7597069afcf863ef0a1` |
| `V6Width29CorrelatedAgreement.lean` | `764d79d83b6d5a38e63aa483c8fc6708adf7d22606bc7a31403fdbf21929452a` |
| `V6OneFoldCandidateExtraction.lean` | `c5b0e705f36b2961c5c2e7edb251fd026edd780a9a3f6c5982d2ac8a124fe8c3` |
| `K1/V7ExactCorrelatedAgreementInitial.lean` | `2ea7bc4075071614cde312e4b48d480ef6af8495f888ca9b8b4ebd12734729a7` |
| `K1/V7ExactCorrelatedAgreementTerminal.lean` | `e8084c02a019c3ad27fd018896f35d9bdc2b9a266d232a4814ba6d84792181c4` |
| `K1/V7ExactCorrelatedAgreementOuterSelection.lean` | `39ba46f483a7c8b92db20577eb7121bec2bfb3ff3c38458c8ec2447c06c41e77` |
| `K1/V7ExactCorrelatedAgreementInterpolation.lean` | `42b96419c5461e61e35a4c7d2d3839019c78b2b3c6e413f3f97176f7982f5a8a` |

## The legitimate three-helper normalization loses support

Fix the actual C1 word and its early optional message tuple `p`, with
`earlyC1 received = some p`. Its joint own support `S` has at least 245,609
complete fibres; as many as 16,535 fibres remain outside it. For nonzero
gamma define, from an **original-code message** `U`,

```
normalized U = gamma^(-26) * (U - c1Batch p gamma).
```

Code linearity preserves original-code membership. On `S`, the literal
received raw batch equals the encoded C1 batch plus `gamma^26` times the
three-helper degree-two curve. Hence every raw agreement fibre retained
inside `S` is a genuine full-domain agreement fibre of that helper curve
with `normalized U`. The code is not punctured; only its matching support
is reduced. This is the correct alternative to subtracting a possibly
incorrect C1 OOD quotient term and calling the result a quadratic curve.

The new [HelperSupportTransfer.lean](experiments/HelperSupportTransfer.lean)
defines the retained set as `S` minus the actual raw mismatch set. It proves
the support-level algebra and composes the existing literal chord/image
reconstruction, which loses at most two pole fibres. In particular:

```
quotient matching >= 26095
  -> retained helper matching >= 26095 - 16535 - 2 = 9558 fibres
  -> >= 38232 actual original-domain symbols.
```

Equivalently the quotient mismatch cap is 236,049. The claim requires the
actual checked OOD data and the literal image equations of the decoded
quotient candidate. It assumes neither polynomiality of the received word
nor provider membership. It does **not** derive that image-valid candidate
or its agreement threshold from acceptance, and it does not finish a
degree-two correlated-agreement theorem port.

Formal status: **kernel-checked deterministic/source-shaped identities**.
The focused replay [helper-support-transfer-v1.log](experiments/helper-support-transfer-v1.log)
passed on its first attempt, with all five endpoint axiom audits limited to
`propext`, `Classical.choice`, and `Quot.sound`. The 26,095 threshold is
sufficient, not asserted necessary or optimal; it preserves complete
fibres rather than attempting a slightly tighter symbol-only pole count.

## Why the previous 9,558-fibre cutoff cannot be reused unchanged

The entire old folding agreement support can lie in the 16,535 excluded
C1 fibres. This is not merely an inequality counterexample. A source-shaped
code/claim diagnostic is:

- Fix `A` of 9,558 complete fibres before all challenges. Put 1 in C1 lane
  zero on `A`, zero elsewhere, and zero in all other C1/helper lanes.
- Take `p=0`. Its actual own support is `univ \\ A`, size 252,586. Encoder
  linearity and `1 != 0` give that support equality. The existing exact
  `EarlyC1Specialization.identify` theorem then identifies the actual
  optional object as `earlyC1 received = some 0`.
- Claim lane-zero value 1 at both OOD points, with all other component
  values zero. The interpolant is the constant 1. The candidate `Q=0`
  satisfies both image equations and reconstructs `U=1`.
- The virtual quotient and `Q` agree on `A` (totalized poles can add
  agreements). But `normalized U = gamma^(-26)` is nonzero everywhere,
  whereas the actual helper curve is zero everywhere.

Thus the proposed implication from the old quotient support to even one
retained helper agreement is false. The indicator fixture itself was not
newly kernel-instantiated or executed through the repaired relation. This
is a deterministic code/claim falsifier, **not an accepting payment proof,
forgery or extractor-failure probability**. In particular, the false C1 OOD
claim still has to survive the actual relation; that is not assumed away.

For a fixed excluded set of the maximum allowed size, fresh uniform
distinct q22 queries all lie in it with exact probability

```
choose(16535,22)/choose(262144,22) = approximately 2^-87.7277130367.
```

The exact rational is greater than `2^-100`. Simply charging this entire
discarded-support event therefore cannot certify 100 bits. Conversely this
event need not be an extraction failure: the existing private C1 decoder
may still recover the witness. No acceptance or soundness probability is
being inferred from this query diagnostic.

## Reproduction, scope and next obligation

[helper_recovery_caps.py](experiments/helper_recovery_caps.py) evaluates
the exact rational controls, one inner dimension count, and support
thresholds; it ran successfully with `python3 -B` (no field enumeration).
[run_helper_support_transfer.sh](experiments/run_helper_support_transfer.sh)
checks the complete imported source/olean closure against the research
base and immutable borrowed V7 pin
`26a9cd4718aae9f9de7ef1c3394fb74a229085d5`, then runs only the changed leaf
with `lean -M7000` and a 7-GiB aggregate-RSS guard. Existing green leaves
are not replayed. No SBF/CU, prover, decoder or full transaction was run.

Command from the research worktree:

```sh
bash docs/research/v8-no-work-100-20260907/experiments/run_helper_support_transfer.sh \
  docs/research/v8-no-work-100-20260907/experiments/helper-support-transfer-v1.log
```

The leaf used Lean 4.32.0 (`8c9756b28d64dab099da31a4c09229a9e6a2ef35`),
Mathlib `81a5d257c8e410db227a6665ed08f64fea08e997`, and the existing cached
dependencies; runner and leaf both exited 0. The timed leaf took 13.66 s,
peak RSS 5,720,850,432 bytes, and zero swaps. No cap was raised. Research
HEAD remained the stated base, and main was observed at
`c7347eefcf767c375040f8f73160995a7886e3ae`; imported main-source bytes were
checked against the older immutable borrowed pin rather than trusting that
moving HEAD.

| Artifact | SHA-256 |
|---|---|
| `HelperSupportTransfer.lean` | `a2e5f98d466ae7543f1e134cf3ded0ef1d415c811034451188ffe1b2cf73595c` |
| `HelperSupportTransfer.olean` | `267fe9b7833e9e4fa316c9bd43d6dce22e2b9c61656b097476d82594a5377b10` |
| Runner | `07ae91b15f979281ddd1cad8ab63d36020b33675895211dfd76424bbd0f76c43` |

The decisive missing link is joint: show that actual accepted **failed
extraction** outside the current represented-final region yields enough
image-valid original-code support *inside the early C1 support*, or bound
the remaining relation/claim event directly. Merely reducing the number
of unknown helper words does not supply this link, and the old caps remain
numerically insufficient even under their optimistic unproved degree-two
port. The current grammar is not ruled out; the full far-final relation
argument, actual replay extraction, payment endpoint, ZK, FS and complete
transaction CU requirements remain separate obligations.
