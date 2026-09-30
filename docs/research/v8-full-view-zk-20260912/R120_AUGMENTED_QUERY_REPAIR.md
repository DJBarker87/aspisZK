# R118–R120: augmented query repair for the two-swap profile

Source base: `3a4a95e8a5f6d5ee1369c37ae6485ea2b32bf757`.
Selected native manifest: `26755a4250ec6075005e840565040414b694deb97fb1830fc95aff2692d34fb6`.

The verifier, wire format, masks, challenges and security parameters are
unchanged. The measured endpoint remains **999,790 / 999,532 CU under the
actual 1M cap**, with only 210 CU margin on the larger fixture. This proof
work does not establish a universal resource bound or full security.

## Source boundary and the failed reuse

R118 imports the selected actual basis constructor, point weights, structured
G coins, chord transpose and extension-polynomial function. Its primal helper
is an exact prefix of the selected source, not a replacement protocol model.
Each test stage verifies every parent source pin and changes only the test,
its Cargo target, and this extracted helper. Release compilation has overflow
checks enabled, two jobs, and a 5/7 GiB zero-swap cgroup.

The old T163 specialization has rank **1**, not 13, under the two-swap map.
A new fixed specialization has rank 13, but its balancing-pivot contribution
makes its low observation map nonzero. Another zero-carry specialization
has rank 10. All three results are retained. They invalidate these proof
routes; they are not themselves attacks on published proofs.

## Augmented section

For the fixed specialization

`z = [1,1,2,3,4,0,2,3,4,2]`, `kappa = 5`, `alpha = 7`,
`(a,b,c) = (7,5,-5)`,

the low map is **constant across blocks**, rather than zero. Add the public
root 1 to the 22 query roots. Interpolate the natural-basis direction in the
first 23 coefficients. Since every natural-basis polynomial evaluates to 1
at 1, the remainder's coefficient sum is 1. Its normalized direction has
coefficient sum zero; the residual observation equals that of `e_d - e_0`.

This changes the proof's correction section only. It does not add a query,
change the prover, resample a used mask, or impose a new hiding assumption.
The root tuple must be distinct and exclude 1. A separate generic lemma
derives the exclusion from the unit-circle equation and nonzero y; the
universal actual-sampler instantiation is still explicit work.

R119/R120 execute 1,173 exact constant-low-map checks and 1,700 observation
comparisons over four source-derived query families. They retain three point
observations and all seven coefficients of **each** channel, not only their
post-beta mixture. The 13 selected columns have a checked inverse; the
reported determinant is `1190787698` over M31.

R119 accidentally inherited the JSON key `low_zero` for a constancy test.
Its nonzero low counts and original artifact are retained. R120 corrects the
schema to `constant_low_map`; the evidence auditor rejects interpreting the
old label as a zero-map claim.

## What Lean proves

The frozen release replay compiles **42 targets with 83 `#print axioms`
audits**, all exit 0. The only reported axioms are `propext`,
`Classical.choice` and `Quot.sound`; no `sorryAx` or new axiom occurs.

- The extra-root interpolation section, its raw-root zeros and its exact
  constant-low transport identity hold for every distinct permitted root tuple.
- Point and complete seven-coefficient relation observations are linear in
  the section, using the retained reversed-slot/quarter convention.
- The fixed code weights agree with the two-swap tensor formulas; the fixed
  transported point weights agree with the bounded source-shaped chord
  transpose. Both channel formulas and the constant low weights are checked.
- The new fixed 13-by-13 matrix has a kernel-checked right inverse. After a
  base-field homomorphism into the target field, the normalized matrix has
  that right inverse for **every** permitted root tuple. No query-family
  sampling is used for this theorem.
- Quotient directions of degree below 31 have source-shaped chord support
  below 127. For an explicit pivot-preserving encoding permutation, their
  inverse-transported masks are balanced and preserve all 271 sparse G coins.
- Generic exact-field opening lemmas retain all four raw fibre values, both
  OOD zeros and the prepared final fold. Circle, nonzero-coordinate and
  denominator premises remain present.

The permutation parameters in the opening/mask lemmas are deliberate: a
T163 theorem is not silently relabelled as a two-swap theorem. The fixed
numeric certificate is tied to actual source executions, but this is not
a complete Rust machine-word refinement or a theorem for all transcript
challenges. The specialization is an algebraic witness, not an accepted
Fiat–Shamir prefix.

## Replay and evidence

The final 42-target replay totals **72.62 seconds** of per-target wall time.
Maximum per-target RSS is **2,610,728 KiB**, with **zero swaps**. All jobs use
`MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, `TasksMax=128`, and reuse
the pinned Lean 4.32.0 cache. The first generic leaf, carry-boundary chunks
and one inverse row were checked before certificate aggregation. Four small
Lean plumbing failures and their original logs remain in evidence. No job
was retried under a raised memory cap.

The [receipt](evidence/r120-augmented-section/receipt.json) records each exact
target, source hash, revision, command, exit, wall time, RSS, swap and axioms.
The [frozen manifest](tools/r120-release-manifest.json) names all 42 targets.
Public source deltas, test output and compiler logs are content-addressed;
no private fixture, wallet key or compiled object is collected.

```sh
python3 docs/research/v8-full-view-zk-20260912/tools/check_r120_evidence.py
```

No unchanged SBF/runtime suite was repeated. The Solana testing/security
checklist keeps canonical parsing, authentication and rejection behavior
outside any purported proof-only saving; this phase changes none of them.

## First remaining proposition

Bind the augmented section to the **complete two-swap source weight map at
arbitrary challenges**, then prove that its fixed-query determinant
polynomial is nonzero with a freshly checked degree bound. The old T163
degree/nonzero result is not an automatic certificate for this map.

After that, justify the exceptional-event law in the actual adaptive shared-
oracle experiment. A polynomial nonzero for each fixed root tuple does not
by itself justify conditioning on query roots that depend on earlier
challenges. This remains one G-residual component of the larger universal
C1/H1/G affine-image compatibility obligation, including p0/p2 and retained
semantic/point/raw/final/relation observations.

Causal posterior simulation, seed/C2 and eight-way commitment composition,
visible failures/retries/publication, coherent pre-beta quotient-pair
extraction, soundness losses and implementation refinement remain open.
The active under-1M-then-full-security goal is **not complete**.
