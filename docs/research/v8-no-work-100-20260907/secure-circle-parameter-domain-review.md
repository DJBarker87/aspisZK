# Exact secure-circle parameter domain

Status: [SecureCircleParameterDomain.lean](experiments/SecureCircleParameterDomain.lean)
is kernel-checked, with nine standard-only axiom audits. It closes the
accepted-domain algebra identified in
[the sequential OOD sampler audit](quadratic-ood-sampler-audit.md), without
asserting the remaining sampling or freshness law.

The actual predicate is `exactSecureCirclePointFromDecoded t ≠ none`.
`admissible_iff` proves this equivalent to `t.im ≠ 0`; the byte-level
`encoded_admissible_iff` proves the same for
`exactSecureCircleParameterMap (encodeTagQM31ExactLE t)`.

The proof reuses the literal V7 map, including its singular-first inverse
check and subsequent CM31 exclusion. The element i is the actual CM31
quadratic generator embedded into QM31. Its square is -1, and symbolic
square factorization gives

`1+t²=0 ↔ t=i ∨ t=-i`.

Both singular values therefore have zero QM31 imaginary coordinate.
`denominator_nonzero` derives `1+t²≠0` from the source's `t.im≠0` condition;
there is no independent nonpole hypothesis and no finite-field enumeration.

The subfield cardinality uses an explicit equivalence: project a
zero-imaginary QM31 value to its CM31 real coordinate, with inverse
`a ↦ (a,0)`. The exact two-coordinate CM31 representation gives P² values,
and the pinned four-coordinate QM31 theorem gives P⁴. Taking the complement
proves

`Fintype.card {t : QM31Exact // Admissible t} = P^4-P^2`.

The singular roots are not subtracted a second time. No parameter inverse,
circle-map injectivity, sequential distinct-point law, random-oracle
coupling, or accepted-proof probability is newly asserted by this leaf.

## Focused evidence

Source parent: `ce36c58168987142d3f07e5d8cba00fb7b1dd05b`. The inherited
higher-Y cache retains its separate research pin
`289d7356c78a4cd493fe61a54f9548f2a0c11298` and borrowed V7 pin
`26a9cd4718aae9f9de7ef1c3394fb74a229085d5`; it was not relabeled or rebuilt.

- [v1](experiments/secure-circle-parameter-domain-nuc-v1.log): exit 1,
  3.04 seconds, 6,659,120 KiB peak RSS, zero swaps. Eight declarations,
  including the singular characterization and exact cardinality, already
  checked with standard axioms. Only the encoded wrapper failed: its
  restricted simplifier list omitted the named `Admissible` definition.
  The exact failed source and manifest are retained.
- [v2](experiments/secure-circle-parameter-domain-nuc-v2.log): exit 0,
  3.30 seconds, 6,692,052 KiB peak RSS, zero swaps. The only source repair
  added that explicit definition to the wrapper's simplifier list. All
  nine audits use only `propext`, `Classical.choice`, and `Quot.sound`;
  there are no warnings. All 851 provenance entries passed before and
  after the run.

The resource preflight showed 46,780,305,408 bytes available RAM and no
active Lean/Rust compiler or nontrivial user build scope. The host's
pre-existing 161,300,480 bytes of swap use was not caused by this job.
Both attempts used Tailscale `100.108.41.90` (`nuc.local` only as pinned
host-key alias), MemoryHigh 8 GiB, MemoryMax 10 GiB, MemorySwapMax 0,
CPU 200%, and Lean 4.32.0 `-j1 -M9500`. Depth 200 and 200,000 heartbeats
were unchanged. No package build or unchanged replay occurred.

Exact SHA-256 provenance:

| Artifact | SHA-256 |
|---|---|
| Green source / v2 source snapshot | `82b7e8dc4b29385058390d598228de2f959c7848206e09e94af69ea97829ee77` |
| Green olean | `223039d1833b2a416af7ffa178aa45920d824a6ba607f83f29c74be48188ae9e` |
| v2 manifest | `32e98470ad067ee842f635d83190903b0b599ad4cf6efad4c5b9595272528531` |
| Failed v1 source snapshot | `14dfaa71629ca1c160e040f5f2abc7294fe8bb61e67bdc4cb6544c07f148d566` |
| v1 manifest | `8c88a2ee679fbb9844fd0d9824e9440b2f7a191c5b3086189f5bc7fbb903d729` |
| Inherited runner | `5780e61b4d286905ab912bb6ab8e103a20908f78c11bea415db40a5fad110e52` |

The exact logs, manifests, source snapshots, and green compiled output
are retained under `experiments/`. The source is frozen and the sole
compiler slot released. Existing green files were not edited.
