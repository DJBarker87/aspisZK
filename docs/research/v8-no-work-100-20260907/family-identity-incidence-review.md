# Additive family identity-incidence bound

Source parent: `e969d9fa5378dd1e548c8b64b79a9e76a2270d66`.
Status: [`FamilyIdentityIncidence.lean`](experiments/FamilyIdentityIncidence.lean)
is kernel-checked on the capped NUC runner. Its four audits contain only
`propext`, `Classical.choice`, and `Quot.sound`; there is no `sorry` or new
axiom.

The exact generic target is

    card(union_F G_F) * (a-bbar) <= W*(T-bbar),

assuming a<=T, b_F<=bbar<a, individual incidence bounds

    card(G_F)*(a-b_F) <= W_F*(T-b_F),

and sum_F W_F<=W. Factors and challenge sets need not be disjoint. Empty
families are allowed. There is no multiplier by the number of factors.

`ratio_monotone` proves the cross-multiplied inequality

    (T-b)*(a-bbar) <= (T-bbar)*(a-b).

`common_threshold` multiplies the individual incidence by a-bbar, uses
that inequality, then cancels the positive factor a-b. `family_union_bound`
sums the resulting bounds and applies finite-union cardinality subadditivity.
All arithmetic in this generic leaf is symbolic natural-number arithmetic;
no rational division, field enumeration or concrete parameter power appears.

`polynomial_family_bound` additionally derives the individual bounds from
the existing checked maximal root-support sets and constructed identity
coordinates. It therefore does not require an unexplained per-factor
cardinality estimate. Matching candidates may vary with gamma and later
challenges; the fixed polynomials and the common identity threshold remain
the actual hypotheses.

The domain condition a<=T is needed for the monotonicity direction. Without
it, for example T=2,a=5,b=0,bbar=4,n=1,w=3 satisfies the original incidence
5<=6 but not the proposed weakened bound1<=0. This is not an extra selected
restriction: the intended a=38230 is below T=1048576.

The separate kernel-checked arithmetic leaf
[`FamilyIdentityArithmetic.lean`](experiments/FamilyIdentityArithmetic.lean)
sets bbar=31129 and W=117077, giving

    card(union_F G_F)*7101 <=119119642419,
    card(union_F G_F)<=16775051.

This is enough for100 raw bits under uniform nonzero QM31 gamma. It does not
prove that every actual retained factor satisfies the identity threshold,
instantiate the factor weight budget, supply a sampler law, or remove the
large-identity residual. The independently scoped cubic regression shows
why early-C1 closeness alone cannot discharge that residual.

Its five audits contain only `propext`, `Classical.choice`, and
`Quot.sound`; there is no `sorry` or new axiom. It reuses
the actual `qm31Exact_card` theorem before certifying the closed Nat formula
floor((card(QM31)-1)/2^100)=16777215 and the integer consequence
n*2^100<=card(QM31)-1 for n<=16775051. The only large powers are P^4 and
2^100, handled arithmetically; no field enumeration is performed.

## Focused verification

The first focused attempt was green. It exited0 in3.89s with peak
RSS6,642,456KiB and zero swaps under MemoryHigh8GiB/MemoryMax10GiB,
MemorySwapMax0, CPUQuota200%, Lean4.32.0 and `-j1 -M9500`. Both 905-entry
provenance checks passed; no package or unchanged proof suite was replayed.

```sh
bash /home/dombarker/project-offloads/aspis-higher-y.fMoMeX/run_higher_y_nuc.sh \
  /home/dombarker/project-offloads/aspis-higher-y.fMoMeX \
  FamilyIdentityIncidence family-identity-incidence-nuc-v1
```

- Source SHA256:
  `ee03dfe4702e5c756a0b96cebadf28507e0d65548faaeaf78d81c06f8d9b0cdc`.
- Olean SHA256:
  `f315cad90949d327de20539e771a617e031903def422ee2fd15545ed87a5ce5b`.
- Manifest SHA256:
  `b7978610bcae7975d4ee97fde0a23cd5ef0c70db9864a413088efc96ba06951f`.
- Log SHA256:
  `170d09d973f385f7709471b682c61be0856e751e3b6ce5c21584940a9811f096`.

The arithmetic leaf's first focused attempt also passed. It exited 0 in
3.82 seconds with peak RSS 6,650,348 KiB and zero swaps under the same
cgroup/toolchain settings; both 911-entry provenance checks passed.

```sh
bash /home/dombarker/project-offloads/aspis-higher-y.fMoMeX/run_higher_y_nuc.sh \
  /home/dombarker/project-offloads/aspis-higher-y.fMoMeX \
  FamilyIdentityArithmetic family-identity-arithmetic-nuc-v1
```

- Arithmetic source SHA256:
  `46984295371444584a07e517feaac0f7ea5b621f40bc70c0af15e80c6b0230b1`.
- Arithmetic olean SHA256:
  `24fabbb904c381a809cda51eeff53b6b152525bd4de0683dbaee4657a6275d53`.
- Arithmetic manifest SHA256:
  `265f24cdd4f8bd490437dd31efbde607d517daa6eb7d765b9692451de1ebdf60`.
- Arithmetic log SHA256:
  `d28e7db8dbb0e4d813c2816d6c9aac42927cd7bfa3ff39c41fa8b1f6bbd7efde`.
