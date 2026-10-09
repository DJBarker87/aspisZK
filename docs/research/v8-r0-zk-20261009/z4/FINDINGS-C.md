# Z4c — Libra-tail containment under D13/D14

Base: `a17cd72f812b1b697e736f084040382885616559` (`origin/v8-reference`).
Branch: `codex/z4c-libra-20261009`. This is exact finite-field computation,
not a Lean proof or a production change. The operative decisions are
`LOG.md`, “Lead acceptance of Z4b; decision D14” and “Lead decision D13′”.

**Libra passes (i′) and (ii′) in all 100/100 tests each. Its silent mask
image has rank 1,076 on every one of the 20 vectors. The 26-column control
also passes 100/100 each with rank 1,076. Every semantic-column C1 rank is
112 on both fibre sets. All generic excess supports are empty.**

**Stop/review:** the all-zero and all-one α controls have nonzero excess
against the constructed simultaneous-silence subspace. Their computed ranks
do not attain the full-image upper bound, so these are unresolved full-image
containment cases, not certified Libra counterexamples. No further arithmetic
probe was run after this was observed. α9=1/2 is undefined for the prescribed
normalization. The successful generic gate does not settle these events.

## Source, observations and normalization

The probe retains Z4b's ten genuine pair-forest witnesses, their identical
public statement and afterstate, the five pairs, and its sampled challenges
and eligible/H1 tapes. It calls the real honest builder, copy-helper builder
and `Public::terminal_qm31`. The master seed is
`0x5348f0b9a87835d0`. `summarize-c.py` checks the full printed challenge vectors
and all three pre-normalization terminal diagnostics against `probe-B.log`;
this is an exact replay, not merely a new run with a similar seed.

The observation map now uses `aspis_core::r0::transport::ROW_TO_COEFFICIENT`
for opened symbols and OOD evaluations. Thus a row unit at `r` evaluates
natural-basis coefficient `π(r)`. The three semantic point claims and the
inactive sum remain in row space, as D13′ prescribes. A direct check compares
`eval_message(to_coefficients(t),z)` with the row-space weighted sum, and
checks the inverse permutation, pivot 1023 and all 89 common eligible pads.

Lane 28's transported coefficients 0–27 form `h8`, and coefficients 28–55
form `h9`. The additional terminal term is `h8(a8)+h9(a9)`. A coefficient
unit of degree `d` in `hm`, `m∈{8,9}`, contributes exactly:

| Location | Contribution |
|---|---|
| Mask total | `512·(2 if d=0, else 1)` |
| Round `j<m` | constant `2^(8−j)·(2 if d=0, else 1)` |
| Round `j=m` | `2^(9−j)·X^d` |
| Round `j>m` | constant `2^(9−j)·α_m^d` |

All 56 monomials are checked at four evaluation points in every round,
including the reconstructed coefficient 1, running-claim chain and terminal
value. The fourth weight is coefficient-indexed exactly as requested:
`α8^j` at 0–27, `α9^(j−28)` at 28–55, zero elsewhere. Its claim is included
for every lane, not only D. Each base-field lane consequently has 112 typed
observation coordinates: 16 limbs for the four claims, eight OOD limbs and
88 opened symbols. Balance is a separate source constraint.

For the Libra map,

```
Φ0(v) = p9^v(α9) − maskLinear(y_current^v) − y_h,D^v.
```

The normalized round-only remainder is `s = g − Φ0(g)·d/d(α9)`, with
`d(X)=X−1/2`. The difference used for (ii′) is

```
c(w) − c(w′) − η[O(y_w(0)) − O(y_w′(0))]·d/d(α9).
```

The code checks the resulting terminal identities and the exact inverse
shift. Because the shift changes no claim, this is the requested fixed
payload bijection Ψ_ch, not a witness-specific modification to the common
linear map A. For a round-only `g`, its claim coordinates are zero and
`Φ0(g)=g9(α9)`. The source original terminal never reads D.

The main result uses the pinned D12 remainder including its linear terms.
The derivative-subtracted remainder is retained only as an additional
Z4b diagnostic; it is normalized separately and does not replace A in (ii′).

## Simultaneous silence, including D's new round contribution

It would be incorrect to reuse Z4b's claim that D has zero round factor.
The new matrices explicitly account for the Libra polynomial contributed
by the D word used to cancel the remaining PCS observations.

Take γ=7 in K, as in Z4b's cancellation construction. For a source in lane
`c≠28`, the probe uses the lifted tape

```
T_c = t,                 T_D = −γ^(c−28) t,
round image = oldRound_c(t) − γ^(c−28) LibraRounds(t).
```

Each lane's kernel is formed with balance, all four claim rows, both OOD
rows and all opened symbols simultaneously. Their common linearity ensures
that D has all-zero individual observations as well. The total batched word
is identically zero, so its chord quotient, opening polynomial and final
coefficients are also zero. This avoids both a dense full-codeword matrix and
an assumption that those PCS coordinates are irrelevant.

For (ii′), each semantic/H1 raw difference is first matched by its permitted
eligible or inactive-padding source. The D offset is
`γ^−28·batch(target−chosen sources)`. Its raw observations are zero after
those matches. The probe subtracts the exact tail-round contribution of that
offset before testing the remaining target. This includes the mask-total
coordinate throughout. Semantic sources are M31-linear; G, H1 and D are
QM31-valued with all four M31 basis directions.

These lifts give a constructive subspace of the full silent image. The
initial-zero boundary chain has dimension 1,080 over F, and fixed point and
fourth claims force one further K equation, terminal value zero. Therefore
1,076 is an upper bound. When the constructed matrix reaches 1,076, its rank
is the exact silent-image rank, not just a lower bound. The analogous
initial-retained bound is 1,080.

## Generic results and C1 ranks

| Design | Silent rank, all 20 vectors | (i′) | (ii′) | Derivative diagnostic | Excess |
|---|---:|---:|---:|---:|---:|
| Libra, width 29 | 1,076 | **100/100** | **100/100** | 100/100 | 0 |
| 26-column control, width 45 | 1,076 | **100/100** | **100/100** | 100/100 | 0 |

For both designs, the pure image retaining the initial mask sum has rank
1,080, as does the full-tape conditioned round image. Every five-target
group adds zero excess dimensions, with support `[]` and pivot list `[]`.
All 20 full challenge-vector records and 100 three-way terminal diagnostics
match Z4b exactly.

All reported ranks and excess dimensions are over M31. Coordinate labels
`(j,d,k)` use zero-based round, polynomial degree and tower limb. Degree 1 is
reconstructed from the boundary chain; the matrix retains the initial mask
sum, coefficient 0 and coefficients 2–27 for each round. Excess support means
the reduced representative under increasing-coordinate elimination.

Each entry below held for all 20 challenge vectors (320 column checks per
fibre set).

| Semantic column | Random 22 fibres | `{0,…,21}` |
|---:|---:|---:|
| 0 | 112 | 112 |
| 1 | 112 | 112 |
| 2 | 112 | 112 |
| 3 | 112 | 112 |
| 4 | 112 | 112 |
| 5 | 112 | 112 |
| 6 | 112 | 112 |
| 7 | 112 | 112 |
| 8 | 112 | 112 |
| 9 | 112 | 112 |
| 10 | 112 | 112 |
| 11 | 112 | 112 |
| 12 | 112 | 112 |
| 13 | 112 | 112 |
| 14 | 112 | 112 |
| 15 | 112 | 112 |

The C1 tests include the fourth row on both fibre sets. They use balanced
eligible unit cells and the transported encoder; no unrestricted semantic
source is substituted for the eligible restriction.

The **26-column control** has mask-only exponents 0–25, rotations
`tower(e mod 4)`, and the unchanged G factor. It has no Libra tail. As a
stronger observation control, it retains D13 and the same fourth row on every
control lane, including the added mask-only lanes; its conceptual width is
45. The ordinary zero-round-factor D cancellation applies in that control.
No production layout or width is edited.

## Degenerate controls and α9 = 1/2

| Control (first pair/tape) | Constructed silent rank | (i′) constructed pass | (ii′) constructed pass |
|---|---:|---:|---:|
| `theta=0` | 1,076 | 1/1 | 1/1 |
| `mu=0` | 1,076 | 1/1 | 1/1 |
| `eta=0` | 1,076 | 1/1 | 1/1 |
| `theta=mu=0` | 1,076 | 1/1 | 1/1 |
| `alpha_0=0` | 1,076 | 1/1 | 1/1 |
| `alpha_0=1` | 1,076 | 1/1 | 1/1 |
| `alpha_1=0` | 1,076 | 1/1 | 1/1 |
| `alpha_1=1` | 1,076 | 1/1 | 1/1 |
| `alpha_2=0` | 1,076 | 1/1 | 1/1 |
| `alpha_2=1` | 1,076 | 1/1 | 1/1 |
| `alpha_3=0` | 1,076 | 1/1 | 1/1 |
| `alpha_3=1` | 1,076 | 1/1 | 1/1 |
| `alpha_4=0` | 1,076 | 1/1 | 1/1 |
| `alpha_4=1` | 1,076 | 1/1 | 1/1 |
| `alpha_5=0` | 1,076 | 1/1 | 1/1 |
| `alpha_5=1` | 1,076 | 1/1 | 1/1 |
| `alpha_6=0` | 1,076 | 1/1 | 1/1 |
| `alpha_6=1` | 1,076 | 1/1 | 1/1 |
| `alpha_7=0` | 1,076 | 1/1 | 1/1 |
| `alpha_7=1` | 1,076 | 1/1 | 1/1 |
| `alpha_8=0` | 1,076 | 1/1 | 1/1 |
| `alpha_8=1` | 1,076 | 1/1 | 1/1 |
| `alpha_9=0` | 1,076 | 1/1 | 1/1 |
| `alpha_9=1` | 1,076 | 1/1 | 1/1 |
| `alpha=all_zero` | 1,022 | 0/1 | 1/1 |
| `alpha=all_one` | 1,038 | 0/1 | 0/1 |

The first 24 rows certify containment, with exact silent rank 1,076 and
conditioned rank 1,080. The final two rows require a distinction: the probe
constructs a sufficient zero-batched-word subspace. When its rank falls short
of the upper bound, failure of membership in that subspace is **not** failure
of membership in the entire silent image. No enlarged degenerate matrix or
new repair was computed after observing these misses.

The exact reduced supports of those misses are below; the derivative
diagnostic has the same support as (i′) in both cases.

- **All α=0:** constructed silent rank 1,022 (initial retained 1,026).
  (i′) and its derivative diagnostic each add one dimension, pivot `(7,12,2)`.
  Their common support is
  `{(7,12,2)}` ∪ `{(7,d,k): d=13…16, k∈{2,3}}`
  ∪ `{(7,d,k): d=17…21 or 23…26, k∈{0,2,3}}`
  ∪ `{(7,d,k): d∈{22,27}, k=0…3}`
  ∪ `{(8,2,k): k∈{2,3}}` ∪ `{(8,27,k): k∈{1,2,3}}`.
  The full-tape constructed conditioned rank is 1,049; (ii′) has zero excess
  and is certified by its successful preimage solve. (i′) remains unresolved
  against the entire silent image.
- **All α=1:** constructed silent rank 1,038 (initial retained 1,042).
  (i′) and its derivative diagnostic each add one dimension, pivot `(7,14,2)`.
  Their common support is `{(7,d,2): d∈{14,15}}`
  ∪ `{(7,d,k): d=16…19, k∈{2,3}}`
  ∪ `{(7,d,k): d=20…23, k∈{0,2,3}}`
  ∪ `{(7,d,k): d=24…27, k=0…3}`.
  The full-tape constructed conditioned rank is 1,077; (ii′) adds one
  dimension, supported at `{(7,d,2): d=25…27}`, pivot `(7,25,2)`.
  Both entire-image containment questions remain unresolved.
- **α9=1/2:** denominator zero; Ψ_ch and this normalization are undefined.
  The sampled original terminal defects are nonzero:
  pinned `[1943059236,1732195997,1252723289,1795754121]`,
  (ii) `[1423308251,286622470,1977110786,67265398]`.

No helper-pole abort occurred. The retained domain qualifications are an
active helper pole `χ=compressed_tuple(λ)` (builder abort), γ=0 (outside the
D-cancellation construction used here), and singular/coincident OOD choices
(not enumerated). The consecutive fibre set was explicitly tested and is
full rank under D13. None of these qualifications is assigned a probability
by this probe.


Z4b's controls use its first pair and first noise tape. Their full normalized
round/claim targets are tested against the constructed image. A zero terminal
diagnostic alone is not counted as a pass. No substitute direction or limiting
convention is used at α9=1/2, and no challenge-uniform rank theorem is claimed.

The older sparse H1 control at θ=0, μ=η=1, tape `e₁−e₀`, is covered by the
computed image equality at the same α: its round target has initial sum zero,
and the D14 shift makes its final value zero, placing it in the full
1,076-dimensional silent image. Its derivative remainder is already zero.
This is a consequence of the computed rank and the boundary identities,
not an additional recomputed trace sample or an extra entry in the pass count.

## Evidence and reproduction

On the dedicated Linux host, from this branch:

```sh
systemd-run --user --scope --unit=aspis-z4c-reproduce \
  -p MemoryHigh=3G -p MemoryMax=4G -p MemorySwapMax=0 \
  python3 docs/research/v8-r0-zk-20261009/z4/run.py \
  --out /tmp/aspis-z4c-reproduce --trials 20 --seed 5348f0b9a87835d0
```

The isolated Cargo profile uses `opt-level=3`, overflow checks, and its locked
dependencies. A focused `--preflight` preceded the arithmetic run. The
arithmetic work is terminal-polynomial evaluation and conditioned finite-field
elimination. Generic challenge vectors are admitted sequentially; a failed
Libra gate, low random-set C1 rank or helper abort terminates the process
before a later vector is computed.

| Scope / target | Exit | Wall seconds | Peak child RSS (KiB) | Cgroup peak (bytes) | Swap peak (bytes) |
|---|---:|---:|---:|---:|---:|
| preflight / compile | 0 | 48.388371 | 535,896 | 870,240,256 | 0 |
| preflight / probe | 0 | 0.029101 | 17,776 | 870,240,256 | 0 |
| final / compile | 0 | 0.025161 | 28,668 | 24,383,488 | 0 |
| final / probe | 0 | 2423.473170 | 40,232 | 53,866,496 | 0 |

Cgroup peaks are cumulative within each scope (the preflight probe therefore
inherits the compilation peak). The final arithmetic gate took 2,423.473 s;
its peak child RSS was 39.29 MiB, cgroup peak 51.37 MiB, with no swap.
`rustc 1.94.1 (e408947bf 2026-03-25)` built the isolated release profile.
All 189 compiled-source hashes and 15 decision/research-source hashes were
verified against this worktree. The audit checks all 100 replayed targets,
120 generic result records, 78 control result records, and both C1 sets.

The automatic stop checks govern the 100-sample generic gates and random C1
ranks. The scheduled degenerate controls completed before their output was
reviewed. Their nonzero constructive-subspace excesses triggered the stop
and report disposition; no follow-up containment computation was launched.


At the ten-minute review (probe elapsed 10:42), seven vectors had completed
at roughly 90 seconds each. The optimized process was using one CPU, with
cgroup peak 53,743,616 bytes and swap peak zero. Progress justified continuing
under the existing cap; no cap was raised.

Artifacts: [probe-C.log](probe-C.log), [summary-C.json](summary-C.json),
[evidence-C.json](evidence-C.json),
[SOURCE_MANIFEST-C.json](SOURCE_MANIFEST-C.json), and the executable-source
hash inventory in the evidence. [summarize-c.py](summarize-c.py) audits replay,
counts, ranks, excess supports and local source hashes. Exact source snapshots
and build logs are retained at
`nuc:/home/dombarker/project-offloads/aspis-z4c-20261009/`.

No Lean was run, and neither Lean nor production Rust was changed. No binary
or co-author trailer is part of the commit. `#print axioms` is not applicable.
