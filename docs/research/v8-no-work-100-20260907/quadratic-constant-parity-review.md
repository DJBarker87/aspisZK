# Constant-X parity: fixed OOD coefficient obstruction

Status: kernel-checked in
[QuadraticConstantParity.lean](experiments/QuadraticConstantParity.lean),
with ten standard-only axiom audits. Earlier checked nonsquare, twist
and parity leaves remain frozen.

## Exact checked endpoint

Fix the source-order polynomial `F ∈ K[X][Z][Y]` before the OOD points.
Assume F is irreducible with Y degree two and characteristic not two.
Let `reordered F` map each coefficient through the actual
`Polynomial.Bivariate.swap` equivalence. Its discriminant is therefore
in `K[Z][X]`, matching the literal parity decomposition

`discriminant (reordered F) = H²R`, with `R.natDegree = 0`.

The theorem `source_fixed_obstruction` constructs, before either point or
answer,

`E = (swap H).leadingCoeff ∈ K[X]`, `E ≠ 0`, `deg E ≤ degX H`.

For any two OOD points and any two polynomial answers, both literal
`FactorCoherence.pointSubstitution point answer F = 0` identities imply
`E(point₀)=E(point₁)=0`. The answers need not be fixed before their
respective points; no uniformity or independence law is assumed.
The coefficient index is fixed from the original H, not selected after
a specialization or its possible degree drop.

## Derived bridges, not extra correspondence premises

1. `R.natDegree=0` gives the actual polynomial equality `R=C(R.coeff 0)`.
2. The injective coefficient map `C : K[Z] → K[Z][X]`, followed by the
   fraction-ring map, constructs an explicit ring homomorphism
   `K(Z) → Frac(K[Z][X])` using `IsFractionRing.lift`. Its action on
   polynomial elements is proved.
3. The checked irreducibility/Gauss discriminant theorem gives
   nonsquareness in the larger fraction field. The constant-map bridge
   derives nonsquareness of `R.coeff 0` in K(Z), and H nonzero. Neither
   nonsquareness nor a separately supplied primitive premise is assumed.
4. A literal OOD root of the degree-two polynomial gives
   `(2*a_t*answer+b_t)² = d*(H.eval(C t))²` by the quadratic discriminant
   identity; this square identity is derived rather than supplied.
5. `H.eval(C t) = QuadraticTwistObstruction.atPoint (swap H) t` is proved
   from the actual variable swap. The existing twist theorem then forces
   all coefficients at t to vanish, including the fixed chosen E.
6. The source's original order is transported via actual polynomial
   coefficient maps, preserving irreducibility and Y degree. Its OOD
   identity is definitionally the existing `pointSubstitution` interface,
   not a new abstract evaluation hypothesis.

The degree bound reuses the pinned V7
`coeff_natDegree_le_bivariate_swap_natDegree`; no generated vectors or
concrete field domains are expanded. The parity witnesses are supplied
as the exact output of the already checked decomposition, not as a
post-challenge candidate or component tuple.

## Scope remaining

This is the constant-X remainder branch for quadratic factors only.
The checked parity theorem constructs H/R, but deciding which branch
they occupy is mathematical classification, not an efficient extractor.
The current endpoint consumes irreducibility of the fixed F and both
whole OOD polynomial identities; the existing retained-factor source
classification must provide those hypotheses in the final composition.

No degree-two local helper bound is substituted for the degree-28 claim
error. No adaptive final is frozen early. A paired-root probability bound
requires the actual sequential OOD sampler law and conditioning, which
this leaf does not claim. No global component coverage or payment
extraction follows from the coefficient obstruction alone.

## Focused evidence

The source was developed after the checked higher-Y prerequisites;
the unchanged higher-Y runner retains research cache pin
`289d7356c78a4cd493fe61a54f9548f2a0c11298` and borrowed V7 source pin
`26a9cd4718aae9f9de7ef1c3394fb74a229085d5`. It was not relabeled as a
newer checkout. All 835 per-run overlay records matched before and after
the successful check.

Before launch, the read-only Tailscale reservation check showed
46,769,037,312 bytes available RAM and no active user build scope or
Lean/rustc compiler. The host's pre-existing 161,300,480 bytes of swap
use is not reported as zero; this job's own scope had SwapMax 0 and its
reported swaps were zero.

The exact first attempt
[quadratic-constant-parity-nuc-v1.log](experiments/quadratic-constant-parity-nuc-v1.log)
failed with Lean exit 1 after 3.67 seconds, 6,803,152 KiB RSS and zero
swaps. Two small remaining goals concerned (a) the definition of an
evaluation ring homomorphism after the monomial swap step, and (b) a
rewrite of R that also rewrote R inside its own coefficient expression.
The repair closed the first by symbolic reflexivity and replaced the
second with a directed `congrArg` equality chain. No mathematical
hypothesis or resource limit changed. The incomplete module was not
treated as green.

[quadratic-constant-parity-nuc-v2.log](experiments/quadratic-constant-parity-nuc-v2.log)
terminated with Lean exit 0 and successful postflight: 4.09 seconds,
6,836,944 KiB peak RSS, zero swaps, ten audits using only
`propext`, `Classical.choice`, and `Quot.sound`. The unused `eval₂_pow`
simp-argument warning is retained; no additional replay was run for it.

All NUC transport used Tailscale `100.108.41.90`; `nuc.local` was only
the pinned host-key alias. Limits remained MemoryHigh 8 GiB,
MemoryMax 10 GiB, SwapMax 0, CPU 200%, Lean `-j1 -M9500`, declaration
depth 200 and 200,000 heartbeats. No package or unchanged predecessor
was rebuilt.

- Failed v1 source/snapshot:
  `819911191b47b66053c5c0c7cae93f03151ffd4643ec1c240ce5db2d844cb14a`.
- Failed v1 manifest:
  `ef67c51afde1c86e79ee9cd05f7570c0ed7581c5dfcefb35546a6ac915e7c0fc`.
- Green v2 source/snapshot:
  `8775c12d896a626d1ad587ae5d2c6df3d22559f2965cc8ddbd7807df4a99c09c`.
- Green olean:
  `52207ebd53e29d52a040541549a92a5f8176066676fec51c6949b4d8d5dddb01`.
- Green v2 manifest:
  `97be85a01f8813b9a1f6348f7717f019c5890b6ef024c548e56afc6fd64391f5`.

Both exact attempt snapshots, logs and manifests, plus the successful
compiled output, are retained under `experiments/`. The checked source
is frozen and the serial compile slot has been released.
