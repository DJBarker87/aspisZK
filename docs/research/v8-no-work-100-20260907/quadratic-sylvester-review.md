# Actual square specializations imply the 4-delta count

Working parent: `9bc0ceee408f432c879ff2239e3ec565dedcd409`.
The reused NUC scope retains its creation parent
`289d7356c78a4cd493fe61a54f9548f2a0c11298`; this is not a claim that the new
source was committed there. Borrowed source pin remains
`26a9cd4718aae9f9de7ef1c3394fb74a229085d5`.

The new [QuadraticSpecializationSylvester.lean](experiments/QuadraticSpecializationSylvester.lean)
closes the actual-Sylvester consumer that was explicitly pending in the
frozen [quadratic specialization report](quadratic-specialization-review.md).
It is kernel-checked with five standard-only axiom audits. No frozen leaf,
Rust source, protocol message or production path was changed.

## Exact endpoint

For a field K, let `R` be in `K[Z][X]`, `m>0`, and let every X coefficient of
R have Z degree at most `delta`. Define E as the literal Sylvester
determinant/resultant of `R` and `derivativeX R` with degree allowances
`(2*m, 2*m-1)`.

If `E != 0`, and at every gamma in a finite G there exist c and V with

`V != 0`, `deg V <= m`, and `R(X,gamma) = c*V(X)^2`,

then `|G| <= 4*delta`.

The square witnesses may depend on gamma. The theorem does **not** assume
their family is fixed in advance, nor assume a matrix rank, kernel basis,
invertible change of basis or determinant-multiplicity conclusion. It even
permits `c=0`, covering zero specializations; the **global** resultant must
still be nonzero. The explicit degree allowances are part of the statement.
The later application must relate them to the actual parity polynomial's
degree and preserved leading coefficient.

## What is now derived

The full degree-below-m input polynomial space maps linearly and injectively
to the two bounded Sylvester blocks by

`s -> (s*V, -2*s*V')`.

This uses Mathlib's actual convention `(p,q) -> R*q + R'*p`. Its domain
blocks have degrees below `2*m` and `2*m-1`. The map's monomial basis is
transported through the actual coefficient-basis equivalence, producing m
independent vectors in the literal Sylvester matrix kernel.

`sylvester_map_map` and `derivative_map` establish entrywise specialization;
`toMatrix_sylvesterMap'` and `toMatrix_mulVec_repr` establish the coefficient
map. The previously checked basis extension then constructs an invertible
constant matrix with these kernel columns. Consequently `(Z-gamma)^m`
divides E. No unproved determinant-corank premise remains.

The final theorem consumes the root's green `QuadraticSpecializationCount`,
which reuses the pinned V7 coefficientwise resultant-degree proof. Together
they give `m*|G| <= deg E <= (4*m-1)*delta <= 4*m*delta`, and positivity of m
justifies the resulting `|G| <= 4*delta`.

The five audited endpoints are `bounded_kernel_injective`,
`bounded_kernel_zero`, `exists_actual_independent_kernel`,
`square_specialization_multiplicity` and `square_specializations_card_le`.
All depend only on the standard `propext`, `Classical.choice` and
`Quot.sound` axioms; no `sorry` or new axiom is retained.

## Evidence and reproduction

| Attempt | Exit | Wall | Peak RSS (KiB) | Swaps | Result |
|---|---:|---:|---:|---:|---|
| v1 | 1 | 3.72s | 6806804 | 0 | Only the named `equivFun`/`repr` final rewrite was missing |
| v2 | 0 | 4.05s | 6840732 | 0 | All five audits standard-only; provenance unchanged |

The v2 fix adds the existing `Basis.equivFun_apply` identity; it changes no
mathematical premise or resource limit. Both exact attempt source snapshots,
logs and per-run manifests, plus the green olean, are retained locally under
`experiments/quadratic-specialization-sylvester-nuc-v{1,2}*` and
`experiments/QuadraticSpecializationSylvester.olean`.

Green source SHA-256:
`956bd3e7e82c03ca2e2db8b3a4acda9c08f7ee497f44ea01a8f20e5b1aeb1465`.
Green olean SHA-256:
`35bf78f96bb7a5a4b00c53e23e630f23da20cc0254ed43d0e02bcc714e9e3372`.
The v2 manifest SHA-256 is
`b3d4758cc7275a32463de064ff2b267011eb3075153deec6d172c99c797c0b2f`.

Historical command (the runner refuses to overwrite an existing tag):

```sh
ssh -o BatchMode=yes -o ConnectTimeout=10 -o StrictHostKeyChecking=yes \
  -o HostKeyAlias=nuc.local dombarker@100.108.41.90 \
  'bash /home/dombarker/project-offloads/aspis-higher-y.fMoMeX/run_higher_y_nuc.sh \
  /home/dombarker/project-offloads/aspis-higher-y.fMoMeX \
  QuadraticSpecializationSylvester quadratic-specialization-sylvester-nuc-v2'
```

The NUC ran Lean 4.32.0 with `-j1 -M9500`, MemoryHigh 8GiB, MemoryMax 10GiB,
MemorySwapMax 0 and CPUQuota 200%. Only one V8 compiler ran at a time;
the separately authorized V7 reservation was left untouched. Network access
used Tailscale; HostKeyAlias only reused the verified host key. The runner
verified 809 overlay artifacts before and after v2. Native packages remain
pinned-revision cache boundaries, not replayed package compilation. No cold
dependency build, laptop compiler or unchanged regression was run.

## What this does not prove

For the proposed quadratic-factor bound, one must still construct the
literal discriminant decomposition `D=a*H^2*R`, prove square cancellation
outside the explicit specialization-zero cases, retain content and
leading-coefficient exceptions, and prove the parity resultant nonzero.
That last step needs the correct squarefreeness/separability argument;
perfection of K(Z) is not available. The selected degree-below-characteristic
guard and exact additive Z-degree budget must be instantiated.

The proposed `10*degZ F` gamma count is therefore **not** a proved selected
or global bound yet. The nonsquare constant-X twist branch, Y-degree at
least three, accepted-to-candidate coverage, original-code/payment validity,
authentication/replay, full-view ZK and resource-bounded Fiat-Shamir remain
separate. Mathematical basis existence here is not an efficient witness
extractor. A fixed parent after adaptive C2 is not fixed before lambda/chi.

The single next deterministic consumer is cancellation plus this theorem,
with every `a_gamma`, `H_gamma` and parity-degree/zero guard explicit, followed
by a source-valid decomposition/exception partition. No proof-body or CU
change is proposed: the maximum body remains 40282 bytes. These Lean times
are proof-checking costs, not prover or verifier measurements. No grinding
security contribution is introduced.
