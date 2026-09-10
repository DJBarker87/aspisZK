# Adaptive support-qualified root incidence

Source parent: `e969d9fa5378dd1e548c8b64b79a9e76a2270d66`.
Status: both new leaves are kernel-checked, with thirteen standard-only
axiom audits. No Rust search was launched.
This work replaces the proposed search as the primary higher-Y task; the
completed sampler checkpoint is frozen.

## Exact theorem and causal scope

[`SupportQualifiedRootIncidence.lean`](experiments/SupportQualifiedRootIncidence.lean) fixes a finite coordinate domain D,
finite challenge set G and coordinate polynomials E_i. It constructs

    C = {i in D | E_i = 0 as a polynomial}.

Every gamma may choose an arbitrary support S_gamma within D, of size at
least a, on which E_i(gamma)=0. If every E_i has degree at most W, the
new checked theorem proves the natural-number inequality

    |G| * (a - |C|) <= W * (|D| - |C|).

The proof double-counts incidences outside C and reuses the existing checked
`JointImageGame.root_count`. Natural subtraction is truncated; the inequality
is valid even when a<|C|, but informative only when |C|<a. An additive
version avoids subtraction on the left. The maximal qualifying gamma-set
corollary requires no supplied choice of candidate or support.

Polynomials and C are fixed before gamma. Supports can depend on gamma or
on arbitrary later choices: apply the theorem to one qualifying support per
gamma, or use its maximal root-support set. No candidate is moved before
alpha, and no component family, received-word polynomiality, sampler law,
or successful decoder is assumed. The identity-coordinate count remains a
real prerequisite for a useful numerical tail; the theorem does not bound
that count for arbitrary retained higher-Y factors.

## Singular cubic control and the support bottleneck

Fix distinct predetermined parameters t0,t1 and H(X)=(X-t0)(X-t1), before
any actual OOD draw. Let A(Z)=Z^28 and

    F(X,Y,Z) = (Y-A(Z))^3 - (Z-1)*H(X)^3.

At those two parameters the OOD sections have the fixed polynomial answer A,
and both are singular along that answer. This is a conditional algebraic
control: it does not let the prover choose H after seeing random OOD points
or assert appreciable probability of sampling these predetermined roots.
Whenever gamma-1=c^3,
U_gamma(X)=gamma^28+c*H(X) is a polynomial root. This gives unboundedly many
root-admitting specializations as the field grows, despite fixed degrees.
It is a root-only obstruction, not a support-qualified counterexample.
The prime/irreducibility explanation and the count of cube specializations
are mathematical control reasoning, not part of this leaf's Lean audit.

For the fixed-C1-zero/three-helper received shape

    raw_i(Z) = Z^28 + Z^26*h_i*q_i(Z),    degree(q_i)<=2,

the helper polynomial is Z^2+h_i*q_i(Z), still of degree at most2. The full
raw/answer degree remains28. Substitution in the cubic equation gives

    E_i(Z) = h_i^3 * (Z^78*q_i(Z)^3 - Z + 1).

When h_i is nonzero this is a nonzero polynomial of degree at most84:
its constant coefficient is h_i^3. Thus adaptive candidates with large
matching support cannot exploit the root-only example's large horizontal
root set. For 1048576 coordinates, all h_i nonzero, and at least38230
matches per gamma,

    |G|*38230 <= 84*1048576 = 88080384,
    |G| <= 2303.

[`CubicSupportControl.lean`](experiments/CubicSupportControl.lean) is a separate checked leaf deriving the pullback identity,
nonvanishing, degree and matching implication from that literal raw shape
and cubic root equation, then applying the incidence theorem. It does not
assume the pullback-root correspondence. For h_i=H(x_i), its nonvanishing
premise means the coordinate domain excludes the two OOD parameters.

This generic control does not prove that the actual selected circle encoder
realizes the candidates, that the actual chosen interpolant equals F, or that
an authenticated causal suffix accepts. Nor does it show every higher-Y
factor has zero identity coordinates or degree84 pullbacks. There is no
new global probability or payment-extraction claim.

## Verification

`SupportQualifiedRootIncidence` v2 is green, with five `#print axioms`
outputs containing only `propext`, `Classical.choice`, and `Quot.sound`.
One benign unused-section-variable warning (`DecidableEq J`) is retained.

| Attempt | Exit | Lean wall | Peak RSS (KiB) | Swaps | Result |
| --- | ---: | ---: | ---: | ---: | --- |
| generic v1 | 1 | 2.76s | 6651048 | 0 | Sum-body parentheses and noncomputable filter annotation |
| generic v2 | 0 | 2.94s | 6683348 | 0 | Five standard-only audits; provenance postflight PASS893 |
| cubic v1 | 1 | 2.95s | 6651120 | 0 | Literal degree-78 evaluation simplification reached depth200 |
| cubic v2 | 1 | 3.05s | 6649256 | 0 | Explicit evaluation rewrites alone did not avoid the same reduction boundary |
| cubic v3 | 0 | 3.30s | 6684092 | 0 | Opaque-exponent constant-term lemma; eight standard-only audits; postflight PASS895 |

The v1 sum notation parsed the subtraction outside the sum. Parenthesizing
the summand and marking the polynomial-zero filter noncomputable fixed the
local errors; no mathematical premise, limit or imported source changed.

For the cubic proof, both broad and explicitly listed evaluation rewrites
still let elaboration encounter the literal degree-78 polynomial power.
The replacement `shifted_one_nonzero` proves the nonzero constant-term fact
for an opaque positive exponent n first, then instantiates it at78 and uses
`mul_ne_zero`. This is a symbolic sparse-cell repair, not a larger recursion
or memory allowance. The polynomial identity, degree and matching proofs
were already standard-only in the failed attempts; the full leaf is credited
only after v3. Cubic v3 has no warnings.

Green generic source SHA256:
`369b651e5975c59b3cd7222dc36c73c940ba025f144b8d276f90099f475efcb4`.
Green olean SHA256:
`9a48e2a85c1f460c2f712a25f9eeff954debfece51a6cafde5d416dfd5608644`.
V2 manifest SHA256:
`c0d6287ab4ae34011752c27385fddca1e1c41e815e1cc5b15e40c07a8f4ec3d0`.
Both exact attempt source snapshots, logs and manifests, plus the green
olean, are copied locally under `experiments/` and hash-checked.

Green cubic source SHA256:
`5e6c3a41a3370488f914b59e57cd9215f442e102657ca510fbbb430aca46cc3d`.
Green olean SHA256:
`7ae93d8ab862364cbd9c4aa72d970df49d39f032803ade8ecb76ea84ce2187df`.
V3 manifest SHA256:
`4f9776da0c17ae82eeab7acc649ff028d3a64be181ee9e26af57beb6712bd4f3`.
All three cubic attempt triplets and the green olean are retained locally.

The inherited runner pins research cache `289d7356c78a4cd493fe61a54f9548f2a0c11298`
and borrowed V7 sources `26a9cd4718aae9f9de7ef1c3394fb74a229085d5`, separately
from this source parent above. Lean4.32.0 commit
`8c9756b28d64dab099da31a4c09229a9e6a2ef35`; runner SHA256
`5780e61b4d286905ab912bb6ab8e103a20908f78c11bea415db40a5fad110e52`.
Only Tailscale transport and existing pinned imports were used. Each focused
job had MemoryHigh8GiB/MemoryMax10GiB/SwapMax0/CPU200%, `-j1 -M9500`,
maxRecDepth200 and maxHeartbeats200000. Preflight found no competing build
scope and about46.97GB available. No package or unchanged proof was replayed.
