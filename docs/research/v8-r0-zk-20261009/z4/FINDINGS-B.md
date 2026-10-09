# Z4b: real-trace remainder containment

Base: `e5d4e1a3d6fc87e9d99046165fe5c9f81335ba91`. Computation only, over
M31 and QM31 in tower order `(1,i,u,iu)`. No Lean files were changed and no
Lean command was run. This report does not close a formal or privacy release gate.

**Both containment conditions fail on the sampled genuine traces. The failure
persists for generic nonzero challenges and for the proposed 26-column repair.
There is no successful column count within this repair class: a terminal
point-claim constraint remains even with all leading degrees available.**

## Definitions actually tested

There is a material distinction in the request's two descriptions of the
remainder. At the pinned revision, `D12.lean` explicitly assigns the original
terminal's **entire** change, including its linear terms, to `g`. Its common
`A = PayloadSplit.L ∘ JointTrace.tapeLinear` contains the explicit mask
polynomial and direct observations; it is independent of the witness.
Writing `O_w(t,a)` for the unmasked original terminal on the prepared,
balanced trace with noise `t n`, the two tested round functions are:

- **Pinned D12, primary:** `η [O_w(1,a) − O_w(0,a)]`.
- **Derivative diagnostic:** `η [O_w(1,a) − O_w(0,a) − ∂t O_w(0,a)]`.

For the second diagnostic, the subtraction includes the original's exact
linear part at fixed `w`. That derivative would give a witness-dependent
slope; it is not silently substituted for the pinned common `A` in condition
(ii). Both remainders are tested against the same pure-mask silent image.
Condition (ii) uses the literal pinned `c(w) − c(w')` and common full-tape `A`.

The [extended probe](probe.rs) evaluates the unchanged
`Public::terminal_qm31` pair-forest terminal. It interpolates each of the ten
round polynomials from its 28 integer evaluation points, summing every Boolean
tail. Prefix folding computes the three actual opening geometries efficiently.
Every initial/boundary equation and the direct final terminal evaluation is
asserted. The derivative uses exact value/derivative arithmetic for Poseidon
and six-point interpolation for the remaining degree-at-most-five claim
polynomial. It is independently checked against 26-point interpolation of
the unchanged whole terminal, at one point in every round and at the final
challenge, for every pair and challenge vector. These are field identities,
not finite differences or floating-point approximations.

## Genuine instances and sampled tapes

The fixture is the real
`aspis_prover::pool_v1_pair_forest_honest::tests::transfer_fixture`, through
`compile_and_check_pool_v1_pair_forest_private_transfer_honest_v1`.
At this pin, `tests/state_only_full_proof.rs` itself uses the older
`SpendPublic`/`build_spend_trace_v4` fixture, not a pair-forest transfer.
The probe therefore uses the existing checked **pair-forest** transfer
fixture, also used by its same-statement H1 privacy regression.

Ten distinct valid instances share one exact public transfer and one exact
append/afterstate statement. The pair leaf has two copies of the input note
commitment. At four lower Merkle levels, the sibling equals the current node,
so either direction gives the same root. Instances choose path indices
`(0x54321 & ~15) | (i/2)` and pair-slot direction `i mod 2`, for `i=0,…,9`.
Pairs are `(0,1),(2,3),(4,5),(6,7),(8,9)`. Every compilation checks all of its
real constraint residuals are zero, and every public statement is compared
for equality. These are genuine duplicate-leaf/path witnesses, not arbitrary
trace arrays or changed public statements.

For each of 20 separately seeded pseudorandom challenge vectors, the probe
samples one full eligible M31 noise tape and one full inactive-row QM31 H1
padding tape for each pair's first witness: **100 noise tests and 100 distinct
pair/challenge tests**. The master seed is OS sampled and recorded as
`0x5348f0b9a87835d0`; per-trial seed derivation and every challenge are in the
log. Sampling uses the inherited xorshift generator with field-reduction
rejection. All sampled θ, μ, η and α coordinates are nonzero; α coordinates
also avoid 1. λ, χ, zc, both OOD points and 22 distinct query fibres are sampled.
This is reproducible numerical sampling, not a probability bound.

Eligibility and the 64 active-row masks are checked against the actual
pair-forest inventory. Semantic row 1023 and inactive H1 row 0 are overwritten
by the literal balance rule. H1 is built with the real copy-helper builder
before its padding is added. No helper-pole abort occurred in the samples.

## Results

All 20 challenge vectors completed, with identical rank and support patterns.
A single failing target adds one rank; “excess per group” is the rank added by
all five targets at the same challenge.

| Test | Failures / samples | Conditioned F-image rank | Excess per five-target group |
|---|---:|---:|---:|
| (i), pinned D12 remainder | **100 / 100** | **988** | **5** |
| (i), derivative remainder | **100 / 100** | **988** | **5** |
| (ii), pinned zero-tape difference, full tape | **100 / 100** | **1,080**, initial coordinate retained | **4** |

The machine-readable [summary](summary-B.json) checks all 60 group records,
all 100 three-way terminal witnesses, and their coordinate supports.

Round coordinates use zero-based `(j,d,k)`, with `j=0,…,9`, degree `d`, and
tower limb `k=0,…,3`. The compressed coordinates retain degree 0 and degrees
2–27; degree 1 is recovered from the sumcheck boundary equation. Reported
support is the **reduced quotient representative under increasing-coordinate
elimination**, not the support of the unreduced polynomial.

For both definitions of (i), the union of nonzero quotient coordinates is

```
{ (8,d,k) : d ∈ {25,26,27}, k ∈ {0,1,2,3} }
∪ { (9,d,k) : d ∈ {8,…,27}, k ∈ {0,1,2,3} }.
```

This is a 92-coordinate quotient. The five sampled targets span five excess
dimensions per challenge; this does **not** assert that five samples span all
92 dimensions. The excess pivots are `(8,25,0…3)` and `(8,26,0)`.

For (ii), every raw semantic and H1 target is solvable using its permitted
full-tape source: 80 semantic-lane solves and five H1 solves per challenge.
After subtracting these particular solutions, the remaining conditioned
round/initial-mask image has rank 1,080, and the excess is exactly four
dimensions, supported at

```
{ (9,27,k) : k ∈ {0,1,2,3} }.
```

The initial mask-sum coordinate is included, not discarded. The pure-mask
image retaining that initial coordinate has rank 992; fixing it to zero gives
the stated **988-dimensional** silent image. The full-tape rank 1,080 above
is a conditioned round-image rank, not the rank of the entire disclosed payload.

The per-lane conditioning includes balance, all three point claims, both OOD
claims and all 88 opened symbols. After matching these observations, the
remaining PCS displacement can be canceled by the zero-round-factor D lane:
for any nonzero γ in K (e.g. γ=7), subtract the residual batched word using
`γ⁻²⁸`. Its individual raw observations and inactive sum are zero, so this
preserves the matched observations and fixes the quotient/opening/final
components together. Thus the computation tests simultaneous observations,
not an unconditioned round projection. The retained Z4a natural-index opening
convention is the literal pre-transport map at this pin; the separate D13
transport implementation is not changed here. The terminal witnesses below
use only rounds and point claims and therefore survive a message-index
permutation as well.

## Why adding columns does not repair these samples

For every explicit linear mask source, including eligible semantic columns,
the final round and the disclosed current-point claims obey

```
p_9(α_9) = Σ_c f_c(α) y_current,c.
```

A silent pure mask has zero point claims, hence `p_9(α_9)=0`. In contrast, the
probe checks that **every one of the 100 pinned remainders and every one of
the 100 derivative remainders has a nonzero value there**.

For (ii), apply the linear functional

```
Φ(rounds, claims) = p_9(α_9) − Σ_c f_c(α) y_current,c.
```

It vanishes on the full common `A`. On `c(w)−c(w')`, it is
`η [O_w(0,α)−O_w'(0,α)]`, nonzero in all 100 samples. This also explains the
four-dimensional full-tape excess. The point claims themselves are observed
and cannot be chosen independently to cancel that value.

The candidate uses **26 mask-only M31 columns**, exponents `0,…,25`, with
rotations `tower(e mod 4)`, and the unchanged QM31 G factor `1+L_16^26`.
Their last-round leading degrees cover **every degree 1–27**. The exact
conditioned matrix on the first challenge has silent rank **1,076**, compared
with 988 before repair. Both five-target remainder families still add four
dimensions, at `(9,27,0…3)`.

For every challenge, a separate last-round computation even allows arbitrary
K slopes for all 27 factors. Its span has F-rank 108, exactly the polynomials
of degree ≤27 divisible by `(X−α_9)`. All 100 targets of each remainder type
still fail membership, with excess rank four per five-target group. All 100
(ii) differences also retain their nonzero Φ value with the repaired factors.
Consequently **no finite mask-only column count makes (i) and (ii) hold on
these samples while preserving this common linear A and these point-claim
observations**. Filling missing leading degrees removes 88 dimensions of the
old deficit; it cannot remove the remaining terminal constraint.

## Explicit degenerate-challenge controls

These are direct terminal obstruction tests on the first pair and its sampled
tape, not a claim to enumerate every rank-changing challenge locus. All four
limbs of every value are recorded in `probe-B.log`.

1. **θ = 0:** pinned remainder, derivative remainder and (ii) all retain a
   nonzero terminal obstruction. The old sparse H1-only witness is also
   checked against the real terminal: set μ=η=1 and padding `e₁−e₀` in limb 0.
   Its displacement is `(2−active(α))(eq(α,1)−eq(α,0))`, with value
   `[1062937922,666165094,587589305,16574424]`. Its derivative remainder is zero
   because this particular H1-only displacement is linear.
2. **μ = 0:** all three sampled terminal obstructions remain nonzero.
3. **θ = μ = 0:** all three remain nonzero; the first Poseidon lane still has
   weight θ⁰=1.
4. **One α_j = 0 or 1**, separately for each `j=0,…,9`: all 20 controls have
   nonzero terminal obstructions in all three tests. These are also points
   where the generic prefix-pivot nonvanishing assumptions need rechecking.
5. **All α_j = 0**, or **all α_j = 1**: the pinned remainder's H1-padding
   terminal obstruction remains nonzero; the derivative remainder and this
   pair's (ii) terminal obstruction are zero. A zero terminal diagnostic here
   is not a full containment result.
6. **η = 0:** both round remainders are identically zero, and the original
   contribution to Φ vanishes. This control is not an obstruction. No full
   degenerate-challenge rank conclusion is inferred from the zero diagnostic.

Additional domain qualifications remain explicit: a source active helper pole
`χ = compressed_tuple(λ)` causes the real builder to abort; γ=0 invalidates the
D cancellation used here; singular/coincident OOD choices and structured query
sets can change observation ranks. These were not silently treated as generic
samples or numerically enumerated in this task. In particular, the findings
cannot be repaired by charging only the event θ=0: failure was observed in
all 20 generic challenge vectors too. No bad-challenge probability is assigned.

## Reproduction and evidence

From this worktree on a Linux build host:

```sh
systemd-run --user --scope --unit=aspis-z4b-reproduce \
  -p MemoryHigh=3G -p MemoryMax=4G -p MemorySwapMax=0 \
  python3 docs/research/v8-r0-zk-20261009/z4/run.py \
  --out /tmp/aspis-z4b-reproduce --trials 20 --seed 5348f0b9a87835d0
```

The isolated [Cargo manifest](Cargo.toml) and lock build only the probe and its
real source dependencies with `opt-level=3` and overflow checks. No production
source is edited. Four worker threads share one capped cgroup. Expected heavy
work is terminal-polynomial evaluation and finite-field elimination. The host
had 51 GiB available of 62 GiB and no competing build scope at admission;
the job reserves at most 4 GiB and has `MemorySwapMax=0`.

Host: `nuc`; scope: `aspis-z4b-final.scope`; Rust
`1.94.1 (e408947bf 2026-03-25)`. The exact source revision is the base above
plus the probe/manifest hashes in the receipt. All **187** compiled-source
hashes were checked against the final local files.

| Exact target | Exit | Wall seconds | Peak child RSS, KiB | Job swap |
|---|---:|---:|---:|---:|
| `cargo build --release --locked --manifest-path …/z4/Cargo.toml -j2` | 0 | 3.976 | 236,608 | 0 |
| `probe --trials 20` (four workers, logged OS seed) | 0 | 400.128 | 104,392 | 0 |

The cgroup aggregate memory peak was **150,634,496 bytes**; cgroup swap peak
was **0**. There was no need for a repeated final arithmetic run.

[probe-B.log](probe-B.log) contains all challenge vectors, per-pair terminal
witnesses, ranks, excess supports, repair results and controls.
[evidence-B.json](evidence-B.json) records exact commands, source hashes,
exits, timings, RSS, cgroup peaks and swap. The pinned model sources are listed
in [SOURCE_MANIFEST.json](SOURCE_MANIFEST.json). Exact source snapshots and
build logs are retained at
`nuc:/home/dombarker/project-offloads/aspis-z4b-20261009/final-evidence/`.
`#print axioms`: not applicable; no Lean was executed.

Development history: the first compile caught a `u32`/`u64` fixture-index
mismatch, fixed without changing its values. A focused one-challenge run then
passed all checks. The final run adds the random master seed, 20 challenge
vectors, exact 26-column matrix, source-inventory assertions, derivative checks
in every round and the degenerate controls. No memory-pressure failure, cap
increase, package-wide regression or wallet/account/key operation occurred.
