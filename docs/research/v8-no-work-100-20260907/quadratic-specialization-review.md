# Quadratic higher-Y specialization: multiplicity route

Research parent: `289d7356c78a4cd493fe61a54f9548f2a0c11298`.
Borrowed source pin: `26a9cd4718aae9f9de7ef1c3394fb74a229085d5`.
No production or transcript change. This note concerns only Y-degree-two
prime factors in the retained higher-Y branch of `SelectedLinearCover`.
Y-degree at least three remains separate. No global security or extractor
bound follows from the work below.

## Current formal status

`experiments/QuadraticSpecializationDeterminant.lean` is **kernel-checked**
(NUC v3), with five standard-only axiom audits:

1. Divisibility in selected factors multiplies.
2. If every entry in each selected matrix column is divisible by `h`, then
   `h^|S|` divides the determinant. This uses the symbolic Leibniz expansion,
   not a concrete Sylvester-matrix enumeration.
3. Evaluating `M * C(B)` is exactly `eval(M) * B`.
4. A constant matrix `B` with nonzero determinant, whose selected columns
   actually lie in the specialized kernel, gives
   `(Z-gamma)^|S| | det(M)`.
5. For a nonzero polynomial `E`, multiplicity at least `m` at every member of
   a finite set `G` implies `m*|G| <= natDegree(E)`.

The fourth statement requires **constructed** invertible basis data. It
does not assume that a zero determinant has high multiplicity or that an
unproved rank defect supplies the basis. The Kernel leaf is also green:
its eight audits cover the discriminant identity, explicit kernel,
injectivity/linearity, degree bounds and literal `Polynomial.sylvesterMap`.
The Basis leaf is green as well: its two audits use Mathlib's actual
`Basis.extend`/`indexEquiv` and a proved coordinate-matrix right inverse to
construct the invertible matrix. Its endpoint takes an actual independent
kernel family, not a caller-supplied invertible matrix. The separate
`QuadraticSpecializationSylvester` consumer is still pending: it must bundle
the bounded polynomial kernel into its finite monomial basis, pass through
the actual Sylvester coefficient matrix, and thereby discharge that final
independent-family premise.

All compilation must use the new capped NUC workspace and the parent's
serialized slot; no laptop compilation, old-leaf replay or resource-cap
increase is authorized. Exact commands, snapshots, exits, resources and
axioms are recorded below only after actual runs.

| Target/tag | Exit | Wall | Peak RSS (KiB) | Swap | Scope |
|---|---:|---:|---:|---:|---|
| Determinant v1 | 1 | 1.12s | 2172148 | 0 | Two entrywise-evaluation/Nat-cast glue errors |
| Determinant v2 | 1 | 1.02s | 2171916 | 0 | Only `coe_evalRingHom` rewrite missing |
| Determinant v3 | 0 | 1.08s | 2182204 | 0 | Five audits, only propext/choice/quotient axioms |
| Kernel v1 | 1 | 0.30s | 772872 | 0 | Nonexistent `Mathlib.Tactic.Omega` import; no declarations checked |
| Kernel v2 | 0 | 1.40s | 2423732 | 0 | Eight standard-only audits; erroneous import removed |
| Basis v1 | 1 | 1.07s | 2236592 | 0 | Extension theorem green; missing Matrix notation scope prevented second theorem parsing |
| Basis v2 | 0 | 1.09s | 2248860 | 0 | Two standard-only audits; Matrix notation scope opened |

All exact attempt source snapshots, logs and per-run manifests are retained
as `experiments/quadratic-specialization-{determinant,kernel,basis}-nuc-vN-*`
and corresponding `.log` files. Failed logs are diagnostics, not accepted
axiom audits. Determinant v3 source SHA-256 is
`dd39aa552da3353ad081ecc26ac3df14cde9a5afc5a4604860ea2eddf1f9aa23`;
output SHA-256 is
`c6911ac8f4e0a8f402cacaf0cbb80c0411a938b3a064da03c58a3b3dce9395af`.
Kernel v2 source SHA-256 is
`9f1dab542bfe667989bc5dc9db2699e737030f45146eb6337587562b694dc380`;
output SHA-256 is
`217c4bdf127cc6350208331e64fec8b19c9f6c19a9d240b300f897791a83cbf0`.
Basis v2 source SHA-256 is
`b4b37f641ae8f296d0b67d3b53d153a4120de3dc671856e660d0cc43f49470bd`;
output SHA-256 is
`4b1acadd5640c69eb39da1c2de31335d9f8b37b406b3140b9c8cf34ae90b953e`.
All three green outputs and every failed/successful attempt's exact source,
log and manifest have been copied locally. There are 15 clean audits in
these three leaves; no new axiom or `sorry` is retained in their source.

Reproduction uses the recorded new overlay, one target at a time:

```sh
ssh -o BatchMode=yes -o ConnectTimeout=10 -o StrictHostKeyChecking=yes \
  -o HostKeyAlias=nuc.local dombarker@100.108.41.90 \
  'bash /home/dombarker/project-offloads/aspis-higher-y.fMoMeX/run_higher_y_nuc.sh \
  /home/dombarker/project-offloads/aspis-higher-y.fMoMeX \
  QuadraticSpecializationDeterminant quadratic-specialization-determinant-nuc-v3'
```

This is the historical command, not permission to overwrite its log or rerun
unchanged targets. The runner uses Lean 4.32.0, `-j1 -M9500`, MemoryHigh 8GiB,
MemoryMax 10GiB, MemorySwapMax 0, CPUQuota 200%, per-run source snapshots and
before/after provenance checks. Network traffic goes to the Tailscale IP;
HostKeyAlias only reuses the verified host key. Native Mathlib packages are
pinned-revision cache boundaries, not replayed package compilations. A stale
read-only `nuc.local` cache-presence connection was terminated locally before
the Tailscale-only runs; no remote job or V7 process was interrupted.

## The intended bounded branch, with exceptions retained

Write a fixed quadratic factor as

`F(X,Y,Z) = aF(X,Z)*Y^2 + bF(X,Z)*Y + cF(X,Z)`

and its discriminant as `D = bF^2 - 4*aF*cF`. An actual polynomial root
`F(X,U(X),gamma)=0` implies

`D(X,gamma) = (2*aF(X,gamma)*U(X)+bF(X,gamma))^2`.

This identity is uniform in `U`: `U` may be selected after gamma and alpha.
It does not move the candidate or a final backwards through the transcript.
The source-side prerequisite is the existing same-candidate covered/image
root implication; a zero carried scalar or an arbitrary adaptive final
alone is not that prerequisite.

The proposed polynomial factor decomposition is

`D(X,Z) = a(Z) * H(X,Z)^2 * R(X,Z)`.

Here `a` contains the **entire X-content**, while `H` and `R` are primitive
in X over `K[Z]`. The latter is a statement about the gcd of their X
coefficients, not merely nonzero rational functions. `R` consists of the
odd-multiplicity positive-X factors, hence is squarefree over `K(Z)[X]`.
The decomposition, primitivity, nonzero factors and all degree identities
must be derived; they are not established by these three generic leaves.

For nonzero products, swapping the polynomial variables gives

`degZ D = degZ a + 2*degZ H + degZ R`,

while `degZ D <= 2*degZ F`. A fraction-field decomposition with denominators
does not automatically justify either the primitive-specialization claim
or this literal polynomial degree accounting.

### Nonconstant-X parity part

Let `n = degX R > 0` and `delta = degZ R`. First charge every gamma where
`a(gamma)=0` or `lcX(R)(gamma)=0`. Primitivity of `H` implies that `H_gamma`
cannot vanish identically: otherwise `Z-gamma` divides every X coefficient.
If this primitive normalization is not proved, a nonzero coefficient of H
must supply another explicit exceptional set instead.

Outside these events, cancellation of squares in the polynomial UFD gives
`R_gamma = c*V^2`, with `c` a nonzero field scalar. Degree preservation makes
odd `n` impossible; for `n=2*m`, `V` has degree `m`.

The selected characteristic guard is

`n <= degX D <= 2*degX F <= 229374 < 2^31-1`.

This makes positive-X irreducible factors separable in X. **K(Z) is not
assumed perfect**; the degree-below-characteristic argument is required.
The resultant `E(Z)=Res_X(R, derivativeX R)` must then be shown nonzero.

Mathlib's `Polynomial.sylvesterMap` sends `(p,q)` to `R*q + R'*p`. Thus the
literal kernel family for `R_gamma=c*V^2` is

`p = s*V, q = -2*s*V'`, for `deg s < m`.

Its first component has degree below `2*m`; the second has degree below
`2*m-1`. The map is injective because `V != 0`. This provides `m` independent
kernel vectors, not merely one zero determinant. A constant basis extension
then supplies the determinant theorem's actual `B` and selected columns.
The matrix size is `2*n-1`, giving `degZ E <= (2*n-1)*delta`.

The intended consequence is therefore

`m*|G| <= (2*n-1)*delta`, hence `|G| < 4*delta` when the right side is
positive. Adding the two exceptional sets gives the safe integer bound

`|qualifying gammas| <= degZ a + 5*delta <= 5*degZ D <= 10*degZ F`.

If a coefficient-of-H exceptional set is used instead of primitivity, its
extra `degZ H` charge still fits `5*degZ D` by the literal additive degree
identity above. Neither version is a proved selected endpoint yet.

### Constant-X parity part (quadratic twist)

When `R` is constant in X it is absorbed into `a`, leaving `D=d(Z)*H^2`.
Primeness/primitive Gauss arguments must show that `d` is not a square in
`K(Z)`: otherwise the quadratic F splits over the fraction field.

An actual retained OOD identity at `t`, with polynomial answer `A(Z)`, gives

`(2*aF(t,Z)*A(Z)+bF(t,Z))^2 = d(Z)*H(t,Z)^2`.

If `H(t,Z) != 0`, division gives a square root of d in `K(Z)`, a contradiction.
Thus both retained identities force `H(t0,Z)=H(t1,Z)=0`. This remains valid
when `aF(t,Z)=0`; no uncharged leading-coefficient or simple-root premise is
inserted.

Choose one nonzero Z coefficient `E_F(X)` of H before OOD. Then
`deg E_F <= degX H <= degX F`, and both actual points are roots of E_F.
Existing additive factor-X-degree accounting permits a product over fixed
twist factors of degree at most 114687. The ideal two-point root numerator
would be at most `114687^2`, subject to the actual sampler law and event
precedence. This coefficient obstruction is not yet constructed in Lean.

### Accounting and causality

Summing the proposed non-twist quadratic bound over fixed prime factors uses
their additive Z-degree budget, not a factor-count multiplier. Since the
existing total Y/Z-weight budget is 117077, the proposed gamma numerator is
at most `10*117077 = 1170770`. This is only a **candidate restricted bound**.
No numerical term is added to the release ledger while its decomposition,
kernel/basis/resultant and source applications are unproved.

All F, their decompositions and the OOD obstruction coefficients are fixed
from the pre-OOD parent, not chosen from gamma or alpha. The parent may
depend on adaptive C2; it is not thereby fixed before lambda/chi. The actual
29-component received/claim curve retains degree 28. A degree-two helper
curve applies only after a justified C1 subtraction/on-own-support step;
this route does not replace the full error by that helper degree.

## Diagnostic boundaries

An omitted-H-specialization counterexample is

`D=(Z-1)^2*(X^2-Z), a=1, H=Z-1, R=X^2-Z`.

At gamma=1, D is the zero square while `Res(R,R')=-4*Z` is nonzero in odd
characteristic. Canonical content normalization moves `(Z-1)^2` into a and
charges the event. This is a polynomial-decomposition diagnostic, not an
actual two-OOD/payment forgery.

There is also no deterministic implication from two OOD identities plus a
polynomial specialization root to Y-degree one. For fixed B and nonzero H,

`F=(Y-B)^2-Z^53*H^2`

is irreducible in Y in odd characteristic, but `U_gamma=B_gamma+gamma^28*H`
is a root for nonzero gamma with `gamma^3=1`. OOD points at roots of H have
the honest identity answers `A=B(t,Z)`. This is compatible with a degree-two
helper contribution before the gamma^26 shift. It does not show that the
source's particular chosen parent equals this factor-containing example,
or produce a complete payment-semantic trace. A recoverable root on this
branch contributes no extraction failure merely because its factor is
quadratic.

## Remaining gates and unchanged contract

The next formal consumer must assemble the actual Sylvester coefficient
kernel and feed its independent family to the now-proved basis construction.
The root's separate green `QuadraticSpecializationCount` already reuses the
pinned V7 resultant degree lemma and gives `|G| <= 4*delta` **given** the
nonzero resultant and multiplicity premises. The nonzero/resultant and
decomposition applicability facts remain outstanding. Proving plain
resultant vanishing would not buy the factor-of-m multiplicity saving.
After that, construct the
primitive decomposition and twist obstruction before composing the selected
same-Q classification. Higher Y degrees, accepted-extraction coverage,
authenticated access/replay, payment/source correspondence, full-view ZK and
resource-bounded Fiat-Shamir remain independent obligations.

No new proof values or verifier operations are proposed. The unchanged body
census is `697*16 + 52 + 24 + 22*621 + 2*296*26 = 40282` bytes. There is no new
CU, SBF, proving-time or full-transaction measurement. No grinding security
credit is used.
