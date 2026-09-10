# Image-restricted original injectivity

Status: `experiments/SelectedOriginalInjectivity.lean` is kernel-checked on
the capped NUC runner. Its five audits contain only `propext`,
`Classical.choice`, and `Quot.sound`; there is no `sorry` or new axiom. No
runtime verifier measurement or new probability certificate is claimed.

## Exact deterministic endpoint

`original_injective_on_image` takes the actual `OODInterpolant.Data d`,
`d.Checked`, two natural-coordinate messages `Q,Q' : Fin 1024 → QM31Exact`,
both literal image constraints

```
Q[1023] = 0,     d.b * Q[1022] - d.c * Q[1021] = 0
```

and equality `d.original Q = d.original Q'`. It concludes `Q = Q'`.
Neither image constraint nor `Checked` is inferred from acceptance here.
There is no unrestricted injectivity statement for arbitrary data or
messages outside this image domain.

The proof uses existing source-shaped interfaces in order:

1. `SelectedQuotientOriginal.encoded_original` expresses the same stored
   original symbol as chord denominator times the quotient encoding plus
   the actual interpolant encoding. Equal originals therefore give equal
   quotient symbols wherever that denominator is nonzero.
2. `poleSymbols_card` bounds the literal stored zero-denominator symbols
   by two. The proof retains their complement, at least 1,048,574 symbols;
   it does not assert inverses at all stored points or modify the oracle.
3. V7 `exactInitialEncoder_coordinate_grs` and
   `exactCircleGRSMultiplier_ne_zero` turn these symbol equalities into
   evaluations at the actual distinct `exactCircleGRSPoint` coordinates.
4. Both `exactCircleGRSPolynomial` messages have degree at most 1024.
   A nonzero difference cannot vanish on that many distinct points.
   V7 numerator-map injectivity then identifies the original natural
   coefficient arrays `Q,Q'`.

The small generic helper performs the root count symbolically; it never
enumerates the million-coordinate domain. It uses only the ordinary field
polynomial root bound, not an ambient-code membership substitute.

`regular_qualified_unique` consumes the **exact** new
`SelectedHigherYBranch.Qualified c1 c2 d F gamma Q` predicate for each of
`Q,Q'`, the source circle/west-point conditions, `d.Checked`, and nonzero
`derivativeCurve` at one fixed OOD row. Existing
`SelectedSimpleRootRigidity.original_unique` supplies original equality;
the first endpoint, instantiated at the actual `atGamma d gamma`, supplies
quotient equality. `SelectedComponentGame.checked_atGamma` carries the
check, while the unchanged `b,c` carry the literal image constraints.
There is no caller-supplied polynomial/encoding correspondence.

## Exact pre-alpha uniqueness seam

Fix the actual received/OOD prefix `c1,c2,d`, a factor `F`, an OOD row `r`,
and then `gamma` with nonzero row derivative. If any Qualified quotient
exists, there is at most one. Hence all later `(kappa,tau,alpha)` branches
whose **actual final** is the coefficient fold of a Qualified quotient
for this same `F,gamma` use that same quotient. A mathematical choice of
this quotient depends on the fixed prefix and `F,gamma`, not on alpha.
The final itself may still vary with alpha through its legitimate fold.

This is the missing deterministic prerequisite for a fixed-target cubic
alpha argument at each gamma. The whole-fibre support of that chosen
quotient against the actual received quotient word is then fixed before
alpha. A future joint-tail proof can separate schedules entirely inside
that support from schedules containing a mismatching fibre. It must still
derive the literal fold residual and its nonzero cubic, and use the actual
independent ordered-query law. It must not multiply separate gamma and
query marginal bounds without a joint count.

Important limits:

- The quotient can depend arbitrarily on gamma. This is not a degree-28
  candidate curve or a fixed component tuple, and does not license a
  fixed-target degree-28 gamma-error bound for that adaptive choice.
- Both candidates must belong to the same actual Qualified branch. No
  global accepted-to-covered-family implication is supplied; image-invalid,
  outside-family, other-factor and singular-row events remain separate.
- Early C1 remains fixed at its real early prefix. C2 is not falsely frozen
  before its lambda/chi challenges; only the completed pre-gamma prefix is
  fixed here.
- No efficient extractor, checked payment witness, fresh-challenge law,
  Fiat–Shamir theorem, or numeric security improvement follows from this
  leaf alone. Rho/later-repair charges belong to the later joint event
  composition and must not be paid again per factor or support stratum.

## Source provenance

Working parent: `e969d9fa5378dd1e548c8b64b79a9e76a2270d66`.
Borrowed V7 pin: `26a9cd4718aae9f9de7ef1c3394fb74a229085d5`.
Read-only `git diff --exit-code` against that pin was empty for the two V7
sources below. Existing green leaves are unchanged. Compiled-artifact
closure verification and the focused NUC run remain pending authorization.

| Source | SHA-256 |
| --- | --- |
| New `SelectedOriginalInjectivity.lean` | `f4bf9122dc43eba2266f8fe626b17f66d9849d67689ed7210f3d178217ecdbf8` |
| `SelectedQuotientOriginal.lean` | `700ebf92da605906aea81b7bc453c8d94fad6cfd4f97350fe7801b24058b82a2` |
| `SelectedSimpleRootRigidity.lean` | `8328580e952cbb574f9b823187ac503d546f154b0b95f29cbdf64e5213fb46eb` |
| `SelectedHigherYBranch.lean` | `a933e50a7cde61e00d8c68770d9200cea8656c9d3736edb26fc781ee4c998084` |
| `SelectedComponentGame.lean` | `0d1973474b57b8c5c6c03283c2012c8ec28a562fb00b3b51dd17690bad34645f` |
| V7 `K1/V7Tag73ExactGRSConversion.lean` | `918ff7b5b1933caaf9d343c95936cb3d392d86582ec1cfd10a24161c7cdb60bc` |
| V7 `Pool/AlgorithmicCircleDecoderV7.lean` | `2faaf875cf3237c9409a19bf2bbb2dd3d302288ed24b059aabb90fac5ddd6471` |

Only this new source and review are owned by this task. No existing proof,
production source, runner, imported hardlink, or evidence file was changed.

## Focused verification

The first attempt failed locally at the generic root predicate because the
proof had not unfolded `Polynomial.IsRoot`. The retained repair adds that
one explicit `change`; no statement or bound changed. Attempt v1 exited1 in
5.17s with peak RSS6,802,460KiB. V2 exited0 in5.36s with peak
RSS6,836,428KiB and zero swaps. Both 901-entry provenance checks passed.
One benign unused `DecidableEq I` section-variable warning is retained.

```sh
bash /home/dombarker/project-offloads/aspis-higher-y.fMoMeX/run_higher_y_nuc.sh \
  /home/dombarker/project-offloads/aspis-higher-y.fMoMeX \
  SelectedOriginalInjectivity selected-original-injectivity-nuc-v2
```

The run used Lean4.32.0, `-j1 -M9500`, MemoryHigh8GiB,
MemoryMax10GiB, MemorySwapMax0 and CPUQuota200% over the pinned Tailscale
host. An unrelated separately capped V7 build was preserved.

- Green olean SHA256:
  `102b5e58658ddcaf2436c23fd9986d25a315f9ec518249b132c374c7611e5d06`.
- Green manifest SHA256:
  `ac12b3facc9c2c8ff39bfe32043306b26476ad973c3511367b0c5a1ad86bc634`.
- Green log SHA256:
  `2f7aebcfdb7792552c49d3f47fb9a70866dd0293707993cfb32de0ebbccbbbee`.
