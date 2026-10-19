# Z4a: computational structure and obstructions

Base: `805f9c102f74f16b5e3d21496e108d963ed27d10`. Arithmetic: F = M31,
p = 2^31−1, K = QM31, in the source tower order `(1,i,u,iu)`.
This is a computational investigation, not a Lean proof or a release-gate closure.
No Lean was written or executed.

**The requested 1,080-direction silent preimage family does not exist for the
sampled schedule. The silent pure-mask rank is 988. C1 has full rank 1,728 for
the sampled queries, but rank 1,352 for the valid 22-fibre set `{0,…,21}`.**
There are small obstructions relevant to the actual Z4 statements, beyond
failure to cover an overlarge ambient space; see below.

## Experiment and map correspondence

[probe.rs](probe.rs) is a standalone optimized Rust probe using the unchanged
repository M31/QM31 arithmetic and R0 natural-basis/domain modules. The rank
algorithm uses the streaming column/carry elimination convention of
`crates/aspis-prover/src/state_only_hiding_rank.rs`. It does not invoke the
historical q29 gate as though that gate were the Z4 map: that gate's full
semantic-mask source and its initial-claim convention differ from `Partition.M`.
The cell mask, balance, opening-point, and factor definitions were read from
the pinned source; [SOURCE_MANIFEST.json](SOURCE_MANIFEST.json) records their
hashes. The final log includes all challenges, pivots and small witnesses.

The deterministic xorshift seed is `0x5a346120261009`. All ten alpha coordinates
are outside `{0,1}`. The two OOD points are obtained by circle rational
parametrization over K. The common query set, shared by all columns as in
`HonestView.Challenges.queries`, is:

```
15814, 20697, 32661, 61444, 66170, 86028, 116464, 123616,
167497, 171610, 176056, 185463, 216070, 219511, 223121, 225375,
226565, 229164, 234185, 242908, 255687, 262099
```

A claim or OOD value in K contributes four F coordinates. An opened symbol
of an M31 column contributes one, not four. Thus C1 has
`3*4 + 2*4 + 22*4 = 108` effective observation coordinates per column.
The formal zero-extended `C1Cell → K` codomain is much larger; 1,728 is the
rank of the physically typed, query-supported C1 observation space.

Balancing is literal: the row-0 sample is overwritten in each pure lane;
semantic row 1023 is overwritten. A source cell at an inactive row contributes
`e_r − e_dependent`; a source cell at an active row contributes `e_r`.
In particular, some eligible semantic cells are at copy-active rows, so it
would be incorrect to subtract row 1023 for every eligible cell.

## Round dimensions and ranks

There are 280 K coefficients before constraints. The ten K equations

```
p_0(0) + p_0(1) = 0
p_j(0) + p_j(1) = p_(j−1)(alpha_(j−1))   (j = 1,…,9)
```

have F-rank 40 in the computed coefficient matrix. Therefore the
**initial-zero, degree-at-most-27 displacement ambient has dimension 1,080**.
A convenient free coordinate set is `(j,d,k)` with
`d ∈ {0,2,…,27}` and `k ∈ {0,1,2,3}`. Coefficient 1 is recovered from the
boundary equation; there are 27, not 28, independent coefficients per round.
This dimension is not a claim that the nonlinear set of actual `g` values
spans that whole ambient.

| Source/conditioning | F-rank of round data |
|---|---:|
| Pure masks; 3 point claims + 88 symbols per lane fixed; initial claim retained as an output | 992 |
| Same; initial claim also fixed to zero | 988 |
| Pure masks; also fix both OOD claims per lane; initial claim retained | 992 |
| Same; initial claim fixed to zero | 988 |
| Full `silentRoundMaskMap`, with the remaining PCS observations canceled by D, for nonzero gamma | **988** |

The raw pure tape has 18,432 F coordinates, of which 18 are overwritten by
balance. D has zero round factor. The per-column kernels used in the
computation were:

| Lane | Raw constraints including balance | Kernel dimension |
|---|---:|---:|
| One M31 mask-only column, without OOD | 101 over F | 923 over F |
| One M31 mask-only column, with OOD | 109 over F | 915 over F |
| G or D, without OOD | 92 over K | 932 over K |
| G or D, with OOD | 94 over K | 930 over K |

With OOD included, the individual mask-only round-image ranks, retaining the
initial claim, are
`[60,108,148,184,216,248,308,332,356,380]`; G contributes a 652-dimensional
image. Their joint rank is 992, not their sum. These ranks were unchanged by
adding the OOD constraints for this sample.

To relate the smaller computation to **all** of `nonRound`, use the actual
zero-factor D lane. Given individually raw-silent words `W_c` in columns
16–25 and 27, set

```
W_D = − Σ_c gamma^(c−28) W_c,       gamma ≠ 0.
```

For example gamma = 7 works. All columns use the same queries and OOD points.
D then has zero claims, OOD values, openings and inactive sum, and the batched
word `Σ gamma^c W_c` is identically zero. Its chord quotient, opening
polynomial and final coefficient vector are zero as well, by the definitions
of those linear maps. D changes no round polynomial. Thus the smaller rank
is an upper bound from raw silence and is attained by fully silent tapes;
no dense PCS matrix is needed. This argument uses nonzero gamma and common
queries; it does not assert an identical rank for every challenge value.

Fixing the terminal point claims also forces `p_9(alpha_9)=0`. Even before
examining the factor schedule, this cuts the initial-zero ambient from 1,080
to 1,076. The pure-mask factor schedule loses another 88 dimensions in the
sample. Increasing-order elimination gives round pivot counts

```
[108,108,108,108,108,108,108,108,96,28]  (total 988).
```

These are conditional pivot counts after preceding round coordinates have
been eliminated, not ranks of separate round projections. The last-round
projection alone has rank 44.

## Sparse families and their triangular structure

Write `b_i(r)` for row r's big-endian bits, `ell_0(X)=1−X`,
`ell_1(X)=X`, and `E_j(r)=∏_(i<j) ell_(b_i(r))(alpha_i)`.
For an unbalanced unit cell of value v in column c, the exact round image is

```
v E_j(r) ell_(b_j(r))(X)
  f_c(alpha_0,…,alpha_(j−1),X,b_(j+1)(r),…,b_9(r)).
```

An inactive balanced cell is the difference of this expression at r and at
the dependent row. The Boolean-tail sum collapses to the cell's one suffix.
For mask column `c=16+t`,

```
f_c(a) = tau_(t mod 4) L_0(a)^e_t
(e_0,…,e_9) = (1,3,5,7,9,11,15,17,19,21).
```

For G, `f_G(a)=1+L_16(a)^26`, where
`L_0(a)=Σ(3+22i)a_i` and `L_16(a)=Σ(275+150i)a_i`.
The unbalanced cell's leading coefficient at degree `e_t+1` is

```
v E_j(r) tau_(t mod 4) (2 b_j(r)−1) (3+22j)^e_t.
```

G has the analogous degree-27 entry with `(275+150j)^26` and no tower
rotation. Those factors are nonzero at the sampled alpha; the small integer
slopes are nonzero in M31. Direct coefficient evaluation checked 55 cells,
all 10 rounds and 5 evaluation points per round, and checked all 550 leading
coefficients. These single-cell identities do **not** make the single cell
silent: the circle encoder is not systematic, and avoiding a message row
with the same number as an opened index does not avoid that opening.

For sparse silent sources, the search restricted cells to a fixed low-bit
suffix `r mod 2^b = s`, then formed kernel circuits for balance, the five
claims, the 88 symbols, and the initial mask claim. Each circuit is in one
mask-only column or G. It is lifted with the D compensation above. Every
circuit's raw image was recomputed and checked to be zero.

A fixed-suffix MLE factors into a prefix MLE and a fixed suffix equality
factor. Its zero terminal-alpha claim makes the prefix evaluation zero.
Consequently **all rounds `j ≥ 10−b` vanish**. This is an actual block
triangular structure in the round index, with small raw constraints inside
each block.

| Fixed low bits b | Candidate support, M31 column | Candidate support, G (K cells) | Cumulative F-rank, processing b downward |
|---:|---:|---:|---:|
| 6 | no nonzero circuits | no nonzero circuits | 0 |
| 5 | none | 29 | 432 |
| 4 | 40–41 | 28–29 | 644 |
| 3 | 45 | 30 | 644 |
| 2 | 45 | 30 | 852 |
| 1 | 67 | 52 | 944 |
| 0 | 111 | 96 | **988** |

The 988 independent circuits actually selected by this search have support
histogram `{29:452, 30:32, 41:192, 45:176, 52:12, 67:80, 96:4, 111:40}`.
Supports count physical cells in the source column before adding D. A G cell
can use four F limbs; D adds at most the same number of K cells. Overwritten
dependent samples need not be supplied in the tape. This is the sparsest
complete **988-dimensional spanning family found by the stated suffix
search**, not a minimum-support theorem. The smallest selected nonzero
rank-contributing sources use 29 G cells.

The selected circuits are sparse and independent; they are not already
scalar triangular in all `(j,d,k)` coordinates. Streaming elimination gives
the displayed 988 pivots by combining them, possibly increasing support and
using multiple source columns. No claim is made that this latter triangular
basis retains the 111-cell bound. A 1,080-element triangular family cannot
be extracted from a rank-988 map.

There is also a particularly simple last-round degree structure. Zero
terminal claims force each column MLE slice to be `lambda_c (X−alpha_9)`.
The last-round image is contained in the K-span of

```
(X−alpha_9) tau_(t mod 4) (A+201X)^e_t       (t=0,…,9)
(X−alpha_9) (1+(B+1625X)^26)                (G).
```

Here A and B are the fixed prefix contributions. The 11 leading degrees are
`[2,4,6,8,10,12,16,18,20,22,27]`, all distinct. Their leading blocks are
invertible tower multiplications times `201^e_t` or `1625^26`; the latter is
`2025105228` in M31. This gives a small block triangular description of the
44-dimensional last-round projection, and exposes why the missing degrees
cannot be supplied by a mask-only single-column construction.

## Actual round-target obstruction

This is more than an ambient rank deficit. In `D12.g`, choose no eligible
noise and choose H1 padding `e_1−e_0`, in tower coordinate 0. Rows 0 and 1 are
copy-inactive; this is exactly the balanced tape with raw row-1 value 1.
Set `theta=0`, `mu=eta=1`. The H1-dependent copy lane is weighted by
`theta^28`, so the original-terminal displacement is

```
Delta F(a) = (2−activeAt(a)) (eq(a,1)−eq(a,0)).
```

It is independent of the underlying semantic trace. The probe computed its
round polynomials (degree at most 2 per variable), checked their initial-zero
boundary chain, and obtained final value

```
[611961981, 1190256920, 1563574789, 1740809108]  in the QM31 tower.
```

This is nonzero, whereas a fully silent pure mask has final value zero.
Adding the four tower multiples of this actual H1 displacement increases the
computed image rank from 988 to 992. `Z4Maps.roundMask_surjectivity` quantifies
all `ch`; the current `Challenges` type imposes no nonzero-theta restriction.
Thus its unrestricted target has a concrete obstruction for any nonempty
instance family. This calculation does not assert a failure rate for a
Fiat–Shamir transcript, nor claim that merely removing theta=0 repairs the
remaining rank deficits.

## C1: ranks, preimages, and a bad 22-fibre set

The map is a direct sum over 16 semantic columns. Its balanced eligible-cell
counts and ranks are:

| Columns | Eligible cells per column | Effective tape coordinates | Random rank | `{0,…,21}` opening rank | `{0,…,21}` total rank |
|---|---:|---:|---:|---:|---:|
| 0–1 | 222 | 221 | 108 | 56 | 76 |
| 2 | 223 | 222 | 108 | 56 | 76 |
| 3–8 | 224 | 223 | 108 | 57 | 77 |
| 9 | 248 | 247 | 108 | 73 | 93 |
| 10 | 249 | 248 | 108 | 74 | 94 |
| 11–15 | 259 | 258 | 108 | 75 | 95 |
| **Total rank** | | | **1,728** | **1,032** | **1,352** |

The two additional tested patterns were `{8192 i : 0≤i<22}`, rank 1,728,
and `{i,i+131072 : 0≤i<11}`, rank 1,352. These are exact finite-field ranks,
not estimates of typical success probability. The counts alone plainly do
not suffice for every query pattern.

For the random set, each column has a 108-column nonsingular minor from
balanced eligible unit cells. The probe constructed and checked all 108
coordinate preimages per column, including zero inactive sum and eligibility
of every supporting cell: **1,728 identity-image checks**. The physical
supports range from 83 to 109 cells. The log records all source pivot rows
and all nonzero pivot values. This yields numerical triangular bases and
coordinate preimages, not a query-independent Vandermonde certificate.

The useful encoder structure is smaller than the full matrix. Write
`r=4h+t`, and `T_u=2 x_u^2−1`. Each fibre's four observations are an invertible
four-by-four sign transform of the four residue-class evaluations

```
Σ_h C_(4h+t) N_h(T_u),       t=0,1,2,3,
```

scaled by `1,y_u,x_u,x_u*y_u`. Here `N_h` is the source natural
Chebyshev-product basis. In column 0, the eligible rows in residues 1 and 2
have `h≡3 mod 4`, giving the common factorization

```
N_(4k+3)(T) = T D_1(T) N_k(D_2(T)),
D_1(T)=2T^2−1,   D_2(T)=2D_1(T)^2−1.
```

For queries `{0,…,21}`, only **six distinct `D_2(T_u)` values** occur. The
four residue-block ranks for column 0 are `[22,6,6,22]`, totaling 56.
For columns 3, 9, 10 and 11 they are respectively
`[22,6,7,22]`, `[22,22,7,22]`, `[22,22,8,22]`, `[22,22,9,22]`.
This explains the deficiency through aliasing of natural-basis evaluations,
not through insufficient total eligible counts.

A compact exact witness uses just fibres 0 and 1. Let `E_(u,s)` denote the
opened symbol in column 0, and do arithmetic modulo 2147483647. Every
balanced eligible-cell image satisfies

```
1077896458 E_(0,0) + 1210646910 E_(0,1)
+1069587189 E_(0,2) + 936836737 E_(0,3)
− E_(1,0) + E_(1,2) = 0.
```

The probe checked this relation on every eligible source column. On the
balanced noneligible displacement `e_1−e_1023`, its value is **1941520597**.
It therefore witnesses failure to cover even the natural balanced-message
observation space, not just an incorrectly counted codomain.

A valid-payment witness pair realizing that displacement was not searched
for. Nevertheless, the current `ZkStatement.HonestProver` record places no
correctness requirement on `build`: constant public output and two builds
`0` and `e_1` in column 0 are admissible at that abstract interface. Its
zero-tape C1 difference is the balanced displacement above, so the present
unrestricted interface cannot justify `c1_surjectivity` for arbitrary such
builders. For a concrete honest builder, actual witness-difference
containment would be a separate obligation; ambient rank failure alone
must not be relabeled a demonstrated valid-spend privacy attack.

## Generic lemma shapes for later work

These are suggested statements, not proofs or implemented Lean declarations.
The present obstructions must be addressed before trying to close Z4.

- **Balanced-cell image:** applying a tape unit gives `e_r−e_d` exactly on
  inactive nondependent rows, `e_r` on active rows, and zero at the overwritten
  tape coordinate. Use an abstract inactive set, not a concrete 1,024-row sum.
- **Single-cell round image:** the `v E_j ell_b f_c` formula above, its
  degree/leading coefficient, and subtraction for balanced cells.
- **Round-coordinate compression:** coefficient 1 is determined by the
  running-claim equation; fixed initial and terminal claims are separate
  codimension-four conditions over F.
- **Suffix support:** factor an MLE into a prefix MLE and a Boolean-suffix
  equality factor; a zero alpha claim annihilates all later rounds.
- **Last-round factor span:** a zero point claim factors the column slice by
  `X−alpha_9`; distinct remaining factor degrees give invertible four-limb
  leading blocks under explicit nonvanishing hypotheses.
- **D cancellation:** a common query/claim kernel is closed under K-linear
  combinations; a zero gamma-batched word has zero chord, opening-polynomial
  and final-fold images. State `gamma≠0` where its inverse is used.
- **Fibre/residue decomposition:** the four-symbol sign transform and
  `N_(4k+3)=T D_1 N_k∘D_2`; express aliasing through transformed query nodes.
- **Restricted evaluation rank:** require the appropriate transformed-node
  separation and a genuine rank condition for the remaining claim rows.
  Eligible counts by themselves cannot replace these hypotheses.
- **Target compatibility:** actual `g` values would need the silent image's
  terminal and further factor-span constraints. The H1 example violates the
  terminal constraint under the current universal challenge quantifier.

## Reproduction and evidence

On a Linux build host, from this checkout:

```sh
systemd-run --user --scope --unit=aspis-z4a-reproduce \
  -p MemoryHigh=2G -p MemoryMax=3G -p MemorySwapMax=0 \
  python3 docs/research/v8-r0-zk-20261009/z4/run.py \
  --all --out /tmp/aspis-z4a-evidence
```

`run.py` stages the unchanged field/R0 modules and compiles both the small
library and probe with `rustc -C opt-level=3 -C overflow-checks=yes`. It records
source hashes, source snapshots, commands, exits, wall times, child peak RSS,
cgroup memory peak and swap. The expected heavy work is raw-kernel and
round-image elimination, not dependency compilation. No production crate is
edited, and no package-wide build is performed.

The final accepted run is recorded in [evidence.json](evidence.json) and
[probe.log](probe.log). Host: `nuc`; scope: `aspis-z4a-final.scope`; caps: 2 GiB
high / 3 GiB max / zero job swap. No other build scopes were active at the
initial reservation check; the host reported 51 GiB available out of 62 GiB.
| Final target | Exit | Wall seconds | Peak child RSS (KiB) | Job swap |
|---|---:|---:|---:|---:|
| Unchanged field/R0 mini-library, optimized | 0 | 0.888 | 151,944 | 0 |
| `probe.rs`, optimized | 0 | 1.727 | 188,276 | 0 |
| `probe --all` | 0 | 110.361 | 97,240 | 0 |

The scope's final aggregate memory peak was 112,234,496 bytes. The final
local source hashes match the accepted receipt. `#print axioms`: not
applicable, because this task contains no Lean execution.

During development, two compile-only attempts failed (standalone nested-module
path resolution, then a moved Rust vector); staging an unchanged mini-library
and retaining the vector correctly fixed them. An intermediate C1 probe
subtracted the dependent row for active eligible sources as well; the final
probe uses the literal inactive-only balance. The corrected focused C1 run
retained all reported ranks. After adding direct identity/preimage checks and
source snapshots, one final consolidated run checked the complete final
probe. No memory-pressure failure or unchanged cap escalation occurred.
