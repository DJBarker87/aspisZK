# Total root count for a fixed discriminant decomposition

Working parent: `9bc0ceee408f432c879ff2239e3ec565dedcd409`; reused NUC-scope
parent: `289d7356c78a4cd493fe61a54f9548f2a0c11298`; borrowed source pin:
`26a9cd4718aae9f9de7ef1c3394fb74a229085d5`.

[QuadraticSpecializationTotal.lean](experiments/QuadraticSpecializationTotal.lean)
is green with four standard-only axiom audits. It removes the H-specialization
guard from the *event being counted*, by charging its actual fixed polynomial
obstruction. It consumes the checked [guarded even](quadratic-guarded-review.md)
and [odd](quadratic-odd-review.md) results without changing either source.

Fix `aF,bF,cF,H,R` in `K[Z][X]`, with `H != 0` and the literal equality
`bF^2 - 4*aF*cF = H^2*R`. Suppose every X coefficient of H has Z degree at
most hDelta and every X coefficient of R has Z degree at most rDelta.
Let G be any finite set whose members each admit an actual polynomial
quadratic root U in K[X]. The witness U is existential separately for each
gamma; neither one fixed U nor a nonadaptive family of final candidates is
assumed.

The exceptional polynomial is constructed as `H.leadingCoeff` (leading in
X, a polynomial in Z). It is nonzero because H is nonzero. If `H_gamma = 0`
as a polynomial, taking the coefficient at the original `H.natDegree`
proves `H.leadingCoeff(gamma) = 0`; this does not require specialization to
preserve degree. Its degree bound is the given coefficient bound at that
same index. Thus at most hDelta members of G have zero H-specialization.

The two total endpoints are:

- `total_even_roots_card_le`: if `m > 0`, `deg_X R <= 2*m`, and the literal
  fixed-size `resultant(R,R',2*m,2*m-1)` is nonzero, then
  `|G| <= hDelta + 4*rDelta`.
- `total_odd_roots_card_le`: if `deg_X R` is odd, then
  `|G| <= hDelta + rDelta`.

Each proof partitions the *same* G into H-zero and H-nonzero classes. The
even result instantiates the earlier scalar factor with the literal constant
one. It retains zero R-specializations and degree drops through the checked
Sylvester consumer; no additional leading-R exception is charged there.
The odd result uses the already constructed leading-R obstruction. Neither
endpoint assumes H-regularity or R-regularity of the full event G.

The remaining two audits are `zero_specialization_forces_fixed_root` and
`zero_specializations_card_le`. All four depend only on `propext`,
`Classical.choice` and `Quot.sound`; no `sorry` or new axiom is retained.

The first focused run passed: exit 0, 3.08s wall time, peak RSS 6833212 KiB,
zero swaps. There was no failed or unchanged repeated attempt for this
leaf. Exact v1 source snapshot/log/manifest and green olean are retained
under `experiments/quadratic-specialization-total-nuc-v1*` and
`experiments/QuadraticSpecializationTotal.olean`.

Source and snapshot SHA-256:
`c2a834141a04514bfb992984eff75b9730896582c3ac24d1a970ae4eb5d69238`.
Olean SHA-256:
`a6b0261c9e3ea944713ac51caae9b05e8c0130cdbb1a34a46c24a431cfc982f3`.
Log SHA-256:
`f37278b8ef4fd19bbdd7979d0ed1596ae9e85a6c05a25b3da5c72acaac89b54e`.
Manifest SHA-256:
`a62fc243fc627ca7fa482c625d76981e4dd2a81d85a104aba25f42f4cab88335`.

Historical command, not an unchanged replay instruction:

```sh
ssh -o BatchMode=yes -o ConnectTimeout=10 -o StrictHostKeyChecking=yes \
  -o HostKeyAlias=nuc.local dombarker@100.108.41.90 \
  'bash /home/dombarker/project-offloads/aspis-higher-y.fMoMeX/run_higher_y_nuc.sh \
  /home/dombarker/project-offloads/aspis-higher-y.fMoMeX \
  QuadraticSpecializationTotal quadratic-specialization-total-nuc-v1'
```

The runner used Lean 4.32.0, `-j1 -M9500`, MemoryHigh 8GiB, MemoryMax 10GiB,
MemorySwapMax 0 and CPUQuota 200%. All 829 overlay artifacts passed before
and after; provenance was unchanged. Native package compilation remains a
pinned-revision cache boundary. The connection used Tailscale; `nuc.local`
was only the verified host-key alias. The sole V8 compiler slot was released
after terminal postflight; no V7 process was changed.

This leaf still takes the fixed decomposition, H nonzeroness, coefficient
bounds, and (for even degree) nonzero resultant as explicit prerequisites.
Their constructed producer and characteristic/localization arguments are
separate dependent work. Constant-X parity, exact source variable mapping,
factor selection before challenges, and acceptance-to-actual-root coverage
are not asserted here. This is a finite algebraic root count, not a complete
soundness or efficient checked-witness extraction theorem. No production,
Rust, transcript, proof-size, CU or prover change was made.
