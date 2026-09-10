# Guarded quadratic roots: cancellation through the actual resultant

Working parent: `9bc0ceee408f432c879ff2239e3ec565dedcd409`.
Reused NUC-scope parent: `289d7356c78a4cd493fe61a54f9548f2a0c11298`.
Borrowed source pin: `26a9cd4718aae9f9de7ef1c3394fb74a229085d5`.

[QuadraticSpecializationGuarded.lean](experiments/QuadraticSpecializationGuarded.lean)
is green. It connects literal quadratic roots to the checked
[Sylvester count](quadratic-sylvester-review.md), using the root's new
`QuadraticSquareCancellation` proof. It does not merely assume that the
specialized parity polynomial is a square.

## Exact statement and exception boundary

Fix `aF,bF,cF,H,R` in `K[Z][X]` and `a` in `K[Z]`, with the literal equality

`bF^2 - 4*aF*cF = C(a)*H^2*R`.

Assume `m>0`, `degX R <= 2*m`, every X coefficient of R has Z degree at most
delta, and the fixed-size resultant `Res(R,R';2*m,2*m-1)` is nonzero.
For a finite G, assume at every gamma in G:

- `a(gamma) != 0` and `H(X,gamma) != 0` as a polynomial;
- some polynomial U is an actual root of
  `aF_gamma*U^2 + bF_gamma*U + cF_gamma = 0`.

Then `|G| <= 4*delta`. The candidate U is existential separately for each
gamma and may be adaptive. No candidate is moved before its selection time.

The proof maps the global decomposition with the actual polynomial ring
homomorphism, derives the discriminant square, uses polynomial divisibility
to cancel H, derives the square root's degree bound, and invokes the actual
Sylvester multiplicity/count theorem. No rational quotient is silently
treated as a polynomial. No rank, determinant-multiplicity or invertible
basis-change assumption remains.

There is **no R_gamma nonzero guard** in the final theorem. If R_gamma=0,
the proof supplies the literal square `0*1^2`, with nonzero polynomial V=1.
Otherwise the checked cancellation theorem supplies V. Likewise even-degree
specialization drops are allowed: V needs degree at most m, not exactly m.
Thus no separate leading-coefficient-root charge is needed in this proved
fixed-even-size branch.

The a/H zero events remain outside G and must be eliminated by valid
primitive/content arguments or charged explicitly. This theorem supplies
neither an unconditional bound nor a proof that the decomposition exists.
The odd-degree parity branch still needs its own leading-coefficient/degree
argument; one cannot pad an odd polynomial to an even-sized matrix and
assume its resultant nonzero.

## Evidence

Focused NUC v1 passed: exit 0, wall 3.02s, peak RSS 6830804 KiB, zero swaps.
All three audits (`specialize_discriminant`, `guarded_root_gives_square`,
`guarded_quadratic_roots_card_le`) contain only `propext`, `Classical.choice`
and `Quot.sound`. No `sorry` or new axiom is retained.

Source SHA-256:
`fbfb99fe4f68df79de0633a191fbe1f0f7f64726e53d3497058e3bede37e9e19`.
Olean SHA-256:
`7a298febe508894142dfbe092c9907686e964e51859c5ab4a73ecc2549a40222`.
Manifest SHA-256:
`4b9a92129cb7eeb3797f6b59df6a17e9882b12fb63c6a62a93e0f44dc568c912`.

The exact source snapshot, log and per-run manifest are retained as
`experiments/quadratic-specialization-guarded-nuc-v1-source.txt`, `.log` and
`-manifest.json`; the green olean is retained locally. The historical command
was:

```sh
ssh -o BatchMode=yes -o ConnectTimeout=10 -o StrictHostKeyChecking=yes \
  -o HostKeyAlias=nuc.local dombarker@100.108.41.90 \
  'bash /home/dombarker/project-offloads/aspis-higher-y.fMoMeX/run_higher_y_nuc.sh \
  /home/dombarker/project-offloads/aspis-higher-y.fMoMeX \
  QuadraticSpecializationGuarded quadratic-specialization-guarded-nuc-v1'
```

Lean 4.32.0 ran with `-j1 -M9500`, MemoryHigh 8GiB, MemoryMax 10GiB,
MemorySwapMax 0 and CPUQuota 200%. The runner verified 815 pinned overlay
artifacts before/after and reported provenance unchanged. Native packages
remain pinned-revision cache boundaries, not replayed compilation. Tailscale
carried the connection; HostKeyAlias only reused the verified host key. The
sole V8 compiler slot was released after completion; concurrent V7 work was
not interrupted.

## Remaining application

The next decisive bridge is a source-valid polynomial discriminant/parity
decomposition with its zero-event partition and a proved nonzero resultant.
The new nonsquare-discriminant and twist lemmas address other deterministic
pieces but do not silently provide this decomposition or separability over
K(Z). The even-degree improvement may reduce the proposed quadratic branch
accounting, but no revised selected/global numerical certificate is claimed
until those prerequisites and fixed-factor composition are proved.

The Y-degree-at-least-three branch, accepted-extraction/source/replay
implications, payment witness, full-view ZK and resource-bounded Fiat-Shamir
remain separate. These are mathematical existence/counting results, not an
efficient extractor. No wire or verifier change was made; the body remains
40282 bytes. No new CU, SBF or proving-time measurement, and no grinding
security credit, is claimed.
