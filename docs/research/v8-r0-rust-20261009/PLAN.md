# R0 in Rust — implementation plan (lead, 2026-10-09)

v8 is R0. The proved protocol (`v8-wide-reference-20261005/R0_SOUNDNESS.md`,
formalised in `R0/`, `Wide/`, `R0FS/`, `R0C/`, `R0P/`, `R0Z/`) is the
specification; the Rust is built to it. The existing state-only / pair-forest
code supplies R0's semantic layer (rows 0–24: trace, C1/C2, zerocheck,
masked sumcheck, terminal). Its PCS is the v7-style four-fold QM31 opening
layer and is **replaced**, not refined. Where the Lean and the paper differ,
the Lean is the spec (quarter normalisation, D in the initial commitment,
samplers).

## What the Rust implements (rows 25–31 and the samplers)

Field `E = WideExact = QM31[v]/(v² − u)`, |E| = P⁸, limbs `(c0.c0.a … c1.c1.b)`
= eight M31 in base-P digit order (`R0C/ModuloField.lean:digitsField`).

Samplers, all from one 32-byte transcript block unless stated
(`R0C/ModuloField.lean`, `R0P/SemD2.lean:179–206`, `R0P/CircleSampler.lean`,
`R0C/V3/DuplexQ.lean`, `R0C/V3/Q22Law.lean`):
- semantic rows 0–24 (λ, χ, θ, zc₀…₉, μ, η, α₀…₉): block rank mod P⁴ →
  four base-P digits → QM31 (`qm31Sample`); **no per-limb rejection, no
  nonzero filter**;
- circle rows 25–26: `qm31Sample` parameter → rational map; on `t ∈ CM31`
  the fixed fallback `t₀=(0,1)` / `t₁=(1,1)` (already in `transcript.rs`);
- γ (row 27): block rank mod (P⁸−1), plus one → nonzero E (`gammaNZ`);
- κ, τ, α₀ (rows 28–30): block rank mod P⁸ → E (`ordinary`);
- S (row 31): `Q22.scanOut` — up to 8 (squeeze, advance) block pairs, 18-bit
  words, at most 64 draws, 22 distinct fibres of `Fin 2^18`; exhaustion ⇒
  reject (`cardOK`).
Transcript framing: one absorb of the row's message encoding, then the
sampler (`Duplex.Params`); the proof encoding `p.enc` is ours to fix and is
recorded in SPEC.md.

Codes (`Wide/InitialEncoder.lean`, `Wide/FinalEncoder.lean`,
`R0/Fold`, `R0/RoundNormalization`): initial encoder `K¹⁰²⁴ → K^{2²⁰}`
(the Lean `exactInitialEncoder` directly: message indexed by trace row, Chebyshev-product natural basis, blowup 2¹⁰ — **no R16 transport**; corrected after S1), 2¹⁸ fibres of four
points; `foldWord α` (φ on each fibre, powers of α); final encoder
`E²⁵⁶ → E^{2¹⁸}` (`exactCircleX/Y`); `citedDualFold` with the explicit
quarter.

Chord (`R0/Chord.lean`, `ChordImage`, `ChordGeometry`, `FunctionalWeights`):
`L z0 z1` (no domain zero for distinct non-base points), `interpolant z0 z1 y`
(degree-one message), `secantA/B/C`, `quotientWeights`, image functionals
`e1`, `e2`.

Protocol after the semantic phase (`R0FS/Protocol.lean:40–60,130–135`,
`R0/OpeningDefinitions.lean`):
- row 25: z₀; prover sends `y₀ : Fin 29 → E`; row 26: z₁; prover sends `y₁`
  (message `.values y`, 29×2);
- row 27: γ ≠ 0; prover sends `v ∈ E` (sum of the batched message over the
  inactive rows, `indicator D.inactive`);
- row 28: κ; row 29: τ (message `.unit`);
- prover sends `P ∈ E[X]`, six coefficients, `c₄` reconstructed by the
  verifier from `c₀ + c₄ = ¼·claim′`; row 30: α₀;
- prover sends `F ∈ E²⁵⁶`; row 31: S; prover opens all 29 lanes on the four
  points of each fibre in S with authentication.
Verifier (`Accept`): semantic ∧ authentic ∧ `natDegree P ≤ 6` ∧
`c₀ + c₄ = ¼·claimPrime` ∧ V1 (`∀ u ∈ S, Fin(F)(u) = Fold_α(R_γ)(u)`) ∧
V2 (`P(α₀) = ¼·⟨F, DualFold_α(w_tot)⟩`), with `R_l = (W_l − Enc(I_{y_l}))/L`,
`R_γ = Σ γ^l R_l`, `w_κ = Σ_j κ^{j+1} eq(P_j) + 1_I`,
`claim = Σ_j κ^{j+1} Σ_l γ^l y^{pt}_{j,l} + v`,
`claim′ = claim − ⟨w_κ, msg(I_γ)⟩`, `w_tot = qWeights(w_κ) + τ e₁ + τ² e₂`.

Commitments: lanes 0–25 over F (16 semantic + 10 mask-only) and lane 28 (D,
over K) committed before λ, χ; lanes 26 (H1) and 27 (G) after λ, χ
(`R0P/SemView.lean:c2Words`, `TypedContext.W`; the paper's "three over K
after λ, χ" is superseded). Point claims: 3 × 29 (87). Merkle arity is
immaterial to the proof; reuse the proved eight-way tree (R552).

## Jobs

- **S1 (soundness Codex, documentation)**: `SPEC.md` — every definition
  above as an explicit formula with Lean citations, in Rust-facing terms
  (limb orders, index conventions, φ, the R16 transport matrix, exactCircleX/Y,
  secant coefficients, e1/e2, quotientWeights), plus the proof encoding
  `p.enc`/labels we choose, and the full list of constants. No Rust.
- **R-A (Rust)**: `WideExact` arithmetic in `aspis-core::field` (8-limb
  canonical, add/mul/inv/pow, `try_inv`), KATs against Lean (`u` non-square,
  `wideExact_card`), no panics.
- **R-B (Rust)**: R0 transcript: the samplers above on the existing SHA-256
  duplex; `challenge_queries_without_replacement(22, 1<<18, 64)` already
  exists — align its scan with `Q22.scanOut` (8 pairs, 18-bit words).
- **R-C (Rust)**: encoders and fold: initial 2²⁰ encoder with R16
  transport, `fold_word`, final encoder, `dual_fold` (quarter), chord
  objects.
- **R-D (Rust)**: prover opening phase (virtual lanes, batch, v, P, F,
  openings) and verifier `Accept`; integration with the semantic layer's
  point claims (87) and commitments; serialisation.
- **R-E (Rust)**: fixtures, round-trip + corruption teeth, LiteSVM probe
  (re-point M1's probe), CU measurement.
- **Refinement** (later, Lean): per-row seams from `REFINEMENT.md` G01–G11
  for the semantic layer; the opening layer then refines by construction
  (same samplers, same formulas), leaving G14 (authentication) and G18
  (composition).

Stopped: M2 (q22 shape on the four-fold PCS) — wrong target.

## Decisions after S1 (2026-10-09)

- Encoder: implement `Wide/InitialEncoder.exactInitialEncoder` literally
  (SPEC §3); no R16 transport. Chord/quotient arithmetic converts natural ↔
  monomial coefficients with `M_n` (SPEC §3, `CircleNaturalBasis.lean:41–68`).
- Wire format: SPEC §9 proposal P1 is adopted (domain `aspis:r0:20261009:v1`,
  row labels `0xa0+i`, `tag ‖ len_u32le ‖ payload`, E/K/F as 8/4/1 LE limbs).
  Commitments are absorbed as roots; polynomials as fixed 28/6-coefficient
  records. The Lean `Duplex.Params` full-word/unbounded-polynomial encoding
  is route A's abstraction; the bridge is the authentication and parser
  refinement (REFINEMENT.md G14/G07), not a change to either side.

## Decision D13 (2026-10-09, after Z4a): message-index transport reinstated

The "no R16 transport" line above is withdrawn. A fixed permutation
`π : row → coefficient index` (historical rule: pivot 1023 last; the first 89
inactive rows legal in all sixteen semantic columns at indices 0–88; the
remaining rows in increasing order) is applied before the encoder:
`W_l = Enc(t_l ∘ π⁻¹)`; `eqWeight`, `indicator(I)` and the opening weights are
stated in coefficient space (composed with π). Reason: the privacy LOG,
"Lead decisions after Z4a". Job R-G below; the Lean glue change is Z-side.

## Lead acceptance of R-G (c005349eb, evidence 9789ea8b6): D13 transport in Rust

Reviewed `crates/aspis-core/src/r0/{transport,transport_pads,opening,prover}.rs`
against the historical order rule
(`v8-full-view-zk-20260912/tools/r16_basis_transport.rs:10–63`) and D13.
π⁻¹ lists the first 89 rows `r < 1023, r ≠ 1014` that are copy-inactive and
relation-free in all sixteen semantic columns (rows 13…478, three per
sixteen-row block), then the remaining rows increasing, then pivot 1023; the
historical pivot-sum overwrite is correctly absent. `to_coefficients t = t ∘ π⁻¹`.
C1 and C2 commitments encode `t_l ∘ π⁻¹`; endpoints and honest quotients are
evaluated on coefficients; `eq_weight` and `indicator` are coefficient-indexed,
so `OpeningData::weights`, `claim_prime`, quotient/total weights and V2 inherit
π without further change; the 87 semantic claims and `honest_claims` stay over
rows (`row_eq_weight`); `v_honest` equals the row inactive sum (tested).
Table hash `f80af2ab…2213` (π[row], 1024 × u16 LE) in `transport-kat.json`.

Evidence (`results/r0-opening-20261009/TRANSPORT.md`): six gates on `nuc`,
each in its own scope at 4/6 GiB with zero swap, all exit 0; bijection, both
tables, pairing invariance, every Boolean row's weight, every indicator entry,
87 arbitrary claims; statement test re-derives the pads from the live
inventories; full-size round-trip plus all existing corruption teeth; no_std.
The fixture still uses a synthetic semantic boundary (not an end-to-end
payment proof). **Accepted.**

Consequences for R-E: pass row-indexed lane messages to `Commitment::new` and
`prove`; take the before-z1 endpoint record from R-D's `prove` (transported),
not from R-F's raw-row diagnostic builder, which must either be transported or
not reused; semantic row claims unchanged. The Lean side of D13 is decision
D13′ in the privacy LOG (`v8-r0-zk-20261009/LOG.md`).

## Lead review of R-E (7ba72efd1, 805c4eb63, 40d509084): integration accepted; CU not yet measurable

Accepted: `aspis_prover::r0::r0_prove` and `aspis_statement::r0::r0_verify`
compose the R-F semantic rows with the R-D/R-G opening layer on one P1 wire
(95,712 bytes; semantic prefix 12,903, opening view 83,742 overlapping the
row-26 record). C1 commits lanes 0–25 and D before λ/χ, C2 commits H1/G
afterwards, the before-z1 endpoint comes from R-D's transported path (the
R-G handoff requirement), and the two row-26 records are checked equal before
emission. Genuine transfer and withdrawal proofs round-trip natively with
1,894 recorded rejections; strict acceptance, no PoW, no disabled checks.
Prover 5.1 s / 193 MiB; native verifier 61 ms. Evidence
`results/r0-e2e-20261009/REPORT.md`, all jobs capped 4/6 GiB, swap 0.

**Correction to the headline.** "Does not fit one transaction as implemented"
is not established. The SBF binary is invalid: the compiler reports frames of
32–394 KiB against the 4 KiB limit because `Message<E>` (1024 × 32 B) and
`[E; 512]` are passed and returned by value throughout the opening path
(`eq_weight`, `indicator`, `OpeningData::weights/q_weights/total_weights`,
`chord::*`, `check_v1`, `check_v2`), and `NaturalBasis::new(Initial)` holds
two dense 512×512 M31 matrices (2 MiB) against a 256 KiB heap. Every SBF run
died at 17.6k CU in frame 5. The report itself says no CU or split conclusion
follows; the summary sentence overstated it. The verifier's completed CU is
**unmeasured**, as it was before R-E.

**Risk, as an estimate and not a measurement.** V2 applies a 1024-dimensional
weight computation in E = P⁸ (eq weights for three points, the chord-quotient
transpose, the dual fold, the dot with F), and V1 performs 22 fibre folds with
88 E inversions; with E×E at several hundred CU this is plausibly above 1.4M
even after the memory fix. A dense quotient-weight transpose (four 512×512
passes) would alone be tens of millions of CU and is not a candidate on-chain
algorithm. The decision between a CU campaign and a two-transaction split is
the user's; it needs numbers first. Hence R-E2 below measures before it
refactors deeply.

### R-E2 (Rust A): on-chain-shaped verifier and real CU numbers

Base: `origin/v8-reference` ≥ `40d509084`. Verifier-side only: the wire,
the prover's outputs (both fixture proofs byte-identical), the semantic layer
and every check are unchanged; no check is weakened, reordered across the
phase boundary, or made conditional.

1. **Op counts and primitive costs first.** Instrument `r0_verify` natively
   (feature-gated counters or a counting `CodeField` wrapper) to report, per
   phase (semantic, chord/claims, authentication, V1 per fibre, V2): E×E
   multiplications, E×QM31, E×M31, E additions, E inversions, QM31 and M31
   operations, SHA-256 compressions. Measure each primitive's CU in SBF with a
   small loop probe (N operations minus an empty loop), including
   `WideExact::mul`, `mul_qm31`, scalar-by-M31, `try_inv`, QM31 mul, and one
   SHA-256 compression. Report the product as a predicted CU per phase with
   the headroom to 1.3M/1.4M **before** step 3, in `results/r0-e2e-20261009/
   CU-ESTIMATE.md`. If the prediction exceeds 1.4M, continue; the numbers are
   the deliverable.
2. **Memory shape.** No `Message<E>`, `[E; 512]` or `FinalMessage<E>` by value
   on the verifier path: heap (`Box`/`Vec` with `try_reserve_exact`, total
   ≤ 256 KiB with `request_heap_frame`) or streaming per coefficient; frames
   ≤ 4 KiB, and `cargo build-sbf` must report no stack diagnostics for any
   function reachable from the verifier entry. The dense `NaturalBasis` is
   forbidden on the verifier path. `indicator` becomes a constant bit table;
   `eq_weight` is computed by tensor doubling in QM31 (the points are QM31
   values lifted to E) and lifted once.
3. **Structured quotient weights.** Replace the dense `C[a,b,c]ᵀ` by the
   transpose of multiplication by `L = a + bX + cY` expressed in the natural
   basis: `X·N_j` sets bit 0 of `j` when clear and otherwise carries through
   `X² = (D₁+1)/2`, `D_b² = (D_{b+1}+1)/2`; `Y` swaps the parity halves with
   `Y² = 1 − X²`; the monomial truncation of SPEC §5 is a rank-one correction
   from the overflow of the top factor, with a fixed 512-entry M31 table.
   `row(e1)` and `row(e2)` need only rows 510 and 511 of `M_512`, computed
   from the recurrence without the matrix. Equality with the dense reference
   must be tested on **all 1024 unit vectors** (both maps are linear, so this
   is a complete check) and on random inputs, for several `(a,b,c)`; the
   prover may keep the dense path off-chain.
4. **Measure.** Rebuild the `r0-cu-probe` ELF, rerun both fixtures five
   times with phase markers at the 1.4M limit; report completed CU per phase,
   headroom, proof/account sizes. If a complete run needs a higher limit to
   finish, label such runs explicitly as diagnostic and also report the
   natural split points (after semantics; after k fibres; before V2) with the
   state each would carry across transactions. Standard evidence (caps, RSS,
   swap, manifests, logs), `REPORT-2.md`, branch `codex/r0-e2e-re2-20261009`.

Stop list: any wire, prover-output, semantic-layer or check change; heap
above 256 KiB; a reachable function with a stack diagnostic; a unit-vector
mismatch against the dense reference; raising a memory cap; rerunning an
unchanged measurement. D14 (privacy LOG) will later add a sparse fourth
opening weight row and 29 claims; keep `weights` extensible but do not add it
now.

## Lead review of R-E2 (1b65149d6, 46ff7f35c; on `v8-reference` as 6841515e6, ad5b9a0f4): stop accepted; shaped-path estimate; the one-transaction question; R-E3

**Accepted.** (1) The primitive calibration (27 primitives at N=64 and
N=128, 108 transactions, simulation = execution) and the dense-baseline
estimate of 1.034 G CU, correctly labelled explanatory and not a measurement.
(2) The structured quotient transpose: 4,096 unit-vector and 32 random
comparisons against the dense reference for four (a,b,c), rows 510/511 by
recurrence; accepted as the on-chain quotient-weight algorithm. (3) The
shaped verifier (`r0/onchain.rs`, `OpeningView` over the P1 bytes, bit-table
indicator, QM31 tensor eq-weights, modelled heap 121,720 B): both fixtures
accepted natively, the 1,894 rejection cases preserved, the dense path kept
off-chain as reference. (4) The stop was correct: `verify_semantics_heap`
(4,416 B) and `r0_verify` (4,160 B) are reachable frames, the ELF is invalid
and was rightly not executed. Both commits are cherry-picked onto
`v8-reference`; R-E3 bases on that head.

**Lead estimate for the shaped path (an estimate, not a measurement).** I ran
the worker's `r0-counts` natively on the shaped candidate (46ff7f35c, both
fixtures) and priced the exclusive counts with the worker's N=128 SBF
primitive costs: `re2/lead-shaped-counts-{transfer,withdrawal}.json`,
`re2/lead-price-shaped-counts.py`.

| Phase | Shaped CU (transfer) | Dominant terms |
|---|---:|---|
| Semantic | 1,212,821 | 311 E×E, 1,199 K×K, 306 SHA compressions |
| ChordClaims | 475,090 | 254 E×E, 256 SHA compressions |
| Merkle × 22 | 213,982 | 1,562 SHA compressions |
| V1 × 22 | 7,982,741 (362,852 per fibre) | 3,146 E×E (143 per fibre: γ powers and interpolant recomputed per fibre, hoistable to ≈ 10), 8,096 E×F (26 lanes × 4 slots + 256 final coefficients per fibre), 66 E inversions |
| V2 | 11,873,991 | 4,113 E×E (3,072 for the a, b, c scaling of the 1024 quotient weights + 1,024 for the dual-fold dot), 6,138 K×K (eq tensor tables), 3,072 E×K (κ-weighting), 3,840 E×F |
| **Total** | **21,758,623 ≈ 15.5 × 1.4M** | withdrawal 21,748,168 |

With V1's hoisting and nothing else: ≈ 17.5M, about 12.5 transactions. With
a Karatsuba E×E (≈ 1,000 CU) as well: ≈ 14M, about 10. What remains is the
protocol's own arithmetic. V2 is three E×E scalings and one E×E dot over
1024-coefficient E weight vectors (κ, τ, a, b, c ∈ E). V1 is 22 × (104 E×F
lane terms + 256 E×F final-message terms + 4 E inversions). The Semantic
phase alone is 1.2M. Nothing on the verifier side removes these; they change
only with the opening layer's parameters (message length 1024, E-valued
opening challenges, 22 queries, 256 final coefficients), which are the
Lean's. **The verifier of R0 as specified is a 10–16 transaction verifier;
one transaction is not reachable by implementation work.** The choice between
a multi-transaction verifier for R0 as it stands and a change to the
opening-layer parameters (a re-target of the proof) is the user's. R-E3
measures the real numbers so that the choice is made on measurements.

**R-E3 (Rust A): valid SBF build and measured phases.** Base:
`origin/v8-reference` at the head carrying this section. Branch
`codex/r0-e2e-re3-20261009`. Verifier-side only; wire, prover outputs,
semantic formulas, check order and every check unchanged; both fixtures
byte-identical; the 1,894 rejection cases reject identically.
1. Stack: remove the `verify_semantics_heap` and `r0_verify` frames (box or
   split; no arithmetic change). Then classify every remaining stack
   diagnostic by the call graph from `process_r0_cu_probe_instruction`, not by
   name: the reachable set must be empty; list the unreachable ones with the
   reason. `cargo build-sbf` with zero reachable diagnostics is the gate.
2. Hoist per-fibre invariants out of `onchain::check_v1`:
   `powers::<29>(gamma)`, `interpolant(data, gamma)`, the line, α powers;
   compute once in `prepare`, pass by reference. Results bitwise unchanged
   (assert natively against the unhoisted path on both fixtures and the
   rejection cases).
3. Acceptance runs: both fixtures × 5 at the 1,400,000 limit with phase
   markers; report the last completed phase and the CU at abort.
4. Diagnostic runs, labelled DIAGNOSTIC: the same ELF with LiteSVM's compute
   budget raised far enough to complete, one run per fixture (more if they
   differ); report CU per phase (Semantic, ChordClaims, each Merkle(i)/V1(i),
   V2), the total, the SBF heap high-water mark, and measured/predicted
   against the table above. This raises a CU limit for a measurement, not a
   memory cap, and is not an acceptance claim.
5. Standard evidence (own scopes MemoryHigh 4G / MemoryMax 6G / swap 0, RSS,
   cgroup, manifests, logs) under `re3/`, `REPORT-3.md`. No co-author trailer.
Stop and report if: any wire, prover-output, semantic or check change would
be needed; a reachable frame cannot be brought under 4,096 B without changing
arithmetic; runtime heap > 256 KiB; the hoisted path differs bitwise from the
unhoisted; a memory cap would have to be raised; an unchanged measurement
would be rerun. Do not implement multi-transaction continuation; do not add
D14's fourth row (R-H follows T1); do not change E multiplication (Karatsuba
is a separate decision).

## Lead acceptance of R-E3 (d04ecf4b0, cbb98c315, cherry-picked onto `v8-reference`): valid SBF verifier; measured 19.3M CU

**Accepted.** The stack gate passes by call-graph closure, with every
indirect call conservatively allowed to reach every retained function (262
linked functions); the 32 diagnosed functions are absent from the linked ELF,
so the reachable set is empty. The hoisting is bitwise-preserving (native
differential against the frozen unhoisted path, 1,894 rejection cases
unchanged, both fixtures regenerated byte-identical). Heap high-water 131,080
bytes. Acceptance runs: all ten exhaust 1,400,000 CU during Semantic, after
`Parsed`. DIAGNOSTIC runs (same ELF, LiteSVM budget 200M, heap 256 KiB,
memory caps unchanged): transfer 19,335,682 and withdrawal 19,325,526
verifier CU, 13.8 × 1.4M.

| Phase (transfer) | Measured CU | Lead estimate | Ratio |
|---|---:|---:|---:|
| Semantic | 2,693,892 | 1,212,821 | 2.22 |
| ChordClaims | 1,008,549 | 475,090 | 2.12 |
| Merkle × 22 | 641,001 | 213,982 | 3.00 |
| V1 × 22 | 3,476,468 | 7,982,741 (unhoisted) | 0.44 |
| V2 | 11,507,624 | 11,873,991 | 0.97 |
| Total | 19,335,682 | 21,758,623 | 0.89 |

The measurement supersedes the estimate. V2 matched; Semantic, ChordClaims
and Merkle are 2–3× the primitive model, which did not price parsing,
control, allocation or logging; V1's ratio includes the hoisting.

**The measured fact for the user's decision.** R0's verifier, built to the
Lean and shaped for SBF, costs 19.3M CU. The Semantic phase alone (2.7M) is
more than one transaction; V2 alone (11.5M) is more than eight. Options, with
their cost by track (lead view; the choice is the user's):

- **(A) Multi-transaction verification of R0 as it stands.** About 14–16
  transactions with authenticated continuation state. REPORT-2 §"Natural split
  boundaries" lists the coarse points (after semantics; after k fibres; before
  V2); V2 itself must be cut into at least nine pieces, so the state carries
  partial E-vector accumulators (the 1024 weights and the dual-fold dot). No
  Lean change. The system-level state machine, already unformalised, grows a
  continuation protocol bound to the sealed proof and public context.
- **(B) Change the opening layer's parameters in the Lean.** A re-target of
  the proof. The drivers are the 1024-coefficient E weight vectors in V2
  (κ, τ, a, b, c ∈ E) and the 22 × 256 E×F final-message evaluation plus
  22 × 4 × 29 lane terms in V1; each is fixed by the Lean's choice of field
  for the opening challenges and of the message and final lengths. Any such
  change reopens the soundness accounting and replays the chain.
- **(C) Verifier-side only.** Karatsuba E×E saves roughly 1.8M; nothing else
  is material. One transaction is not reachable this way.

Rust A is held until the user decides. R-H (D14 in Rust: lane-28 h cells,
fourth weight row, 29 extra claims, terminal h-terms) follows T1 regardless
of the choice.

## Lead correction after review of the R-E3 options: R0 §8 is the roadmap, not a re-target; exact savings missed; R-E4

The options paragraph above framed any change to the opening layer as "a
re-target of the proof". That was wrong. `R0_SOUNDNESS.md` §1: R0 "is
deliberately uncompressed. It is the ancestor that later optimisations must be
shown to preserve (§8). Size and compute are not constraints here." §8, "What
each later optimisation must prove", lists the planned steps with their
obligations: (1) ρ-batch the q query equations into the relation (+q/|E|,
`badCombinedChallenges_card`); (2) relation rounds 1–3 in place of the direct
dot product in V2 (three degree-6 rounds, +18/|E|; V7 has the analogue);
(3) eight-way Merkle (proved, R552); (4) two-swap order (`inverse_transport`,
`inverseTransport_dot`); (5) sparse-coded G and a second channel ("not
routine": the joint list must not become a product of two lists or the
semantic row falls to ≈ 98.8 bits); (6) channel fold (`quadratic_dot_product`);
(7) native kernels (source refinement); (8) narrow κ, τ to K and 24 → 22
queries (re-evaluate the ledger). "v8 is R0" means the Lean reference is what
the optimised verifier is proved against; it never meant the reference
verifier is the deployed one. Option (B) is the planned path with named
obligations. The user's decision is sequencing: a multi-transaction interim
(A), or straight to §8 after T1/T2.

**Exact, byte-preserving savings missed by R-E2/R-E3 and by the lead
estimate.** None changes challenges, bytes, check order or any check.
- z₀, z₁ are QM31 points embedded in E (`transcript.rs`, `E::from_qm31`), so
  a = x₀y₁ − x₁y₀, b = y₀ − y₁, c = x₁ − x₀ lie in the K subfield by
  construction. `structured.rs` multiplies them with generic E×E (3,072
  products in the quotient transpose); E×K instead saves ≈ 3,072 × 800 ≈ 2.5M
  CU. `Line::line_word` at an M31 domain point is K-valued, so V1's 88
  inversions are K inversions (942 vs 2,120 CU) and the following products
  E×K: ≈ 0.17M.
- The eq tensor builder computes v·x and v·(1−x); r = v·x, ℓ = v − r saves
  3,069 K multiplications ≈ 0.9M.
- Karatsuba at the outer layer of `WideExact::mul` (three QM31 products
  instead of four) on the ≈ 1,900 E×E products that remain: ≈ 0.5–0.7M.
- Semantic phase: R0's semantic phase is "the V8 baseline before R17"; M1 ran
  transcript, terminal and relation in ≈ 580k CU in QM31. R0's measured 2.69M
  is ≈ 1.2M field arithmetic plus parse, handoff and control; porting M1's
  kernels (R60 inverse chain, R218 norm algebra, R91 bounded-width arithmetic)
  behind equality gates plausibly recovers ≥ 1M.
- V2 evaluation order: with a, b, c ∈ K, L^T eq_p and L^T ind are K-vectors
  and the only E scalars are κ^{p+1}, τ, τ²; moving them outside the pairings
  leaves six E×K dots of 1,024 plus K-side work. Several orders land near
  6.5–7M for V2 (from 11.5M); the choice is made by counting every product,
  reduction and memory pass, not one loop.
Exact-work floor after all of these: ≈ 10–12M CU. That is the figure §8
steps 8, 2 and 1 exist to remove.

**R-E4 (Rust A): exact byte-preserving savings with equality gates.** Base:
`origin/v8-reference` at the head carrying this section. Branch
`codex/r0-e2e-re4-20261009`. Verifier-side only; wire, prover outputs,
challenges, check order and every check unchanged; both fixtures
byte-identical; the 1,894 rejection cases reject identically; every change is
gated by a native differential against the R-E3 path (bitwise, both fixtures
and all rejection cases) before it is measured.
1. Subfield chord coefficients: carry `Line{a,b,c}` as QM31 (assert c1 = 0 at
   construction; fail closed otherwise), multiply with `mul_qm31` in
   `structured::quotient_weights` and `check_v2`'s rows 1021–1023; in
   `check_v1` invert `line_word` in QM31 and multiply E×K. Keep the generic E
   path behind the reference feature.
2. Tensor builder: r = v·x, ℓ = v − r.
3. Karatsuba at `WideExact::mul`'s outer layer; equality on 10⁶ random pairs
   and all limb unit-vector pairs natively; SBF primitive measurement as in
   R-E2 (N = 64/128).
4. V2 evaluation order: count E×E, E×K, E×F, K×K, adds, reductions and memory
   passes for at least three orders (current; scalars outside the pairings;
   transpose onto F with G = dF^T F) and report the counts before
   implementing; implement the lowest.
5. Semantic phase: port the M1 kernels that apply unchanged (R60, R218, R91)
   behind equality gates against the current semantic path; no formula or
   order change.
6. Measure: acceptance 5× at 1.4M; DIAGNOSTIC per phase as in R-E3; table
   measured vs R-E3 per phase and per change (one build per change,
   cumulative). `REPORT-4.md`, `re4/`. No co-author trailer.
Stop and report if: any change would alter challenges, bytes, check order or
a check; a differential mismatch; a subfield assertion fails on either
fixture; heap > 256 KiB or any reachable stack diagnostic; a memory cap would
have to be raised; an unchanged measurement would be rerun. No §8 protocol
step (ρ batching, relation rounds, κ/τ narrowing): those are Lean-first.

**Sequencing proposal for §8 (lead view; the user's call).** After T1 and
T2: step 8 (κ, τ to K; arithmetic ledger only; removes the E×K weighting and
most remaining E×E in V2), then step 2 (relation rounds replacing V2's dot
product; +18/|E|; V7 analogue in the tree), then step 1 (ρ-batched queries).
Step 5 last, and only with its joint-list argument.

## Lead decision after user direction (2026-10-09): target one transaction; the reference closes first; gate G_ref; optimisation sequence

**Direction (user).** The target is one transaction: "otherwise v7 is
actually better". The process comes first: a reference known to be 100-bit
sound and privacy-preserving before any protocol optimisation. Both are now
fixed; neither is re-asked.

**Gate G_ref — the reference is closed when all of these hold at the model
level, with standard axioms and recorded replays:**
- (S) `combined_fiat_shamir_masked` replayed with D13′, D14′, D14″ (T1); the
  constant recorded exactly (B3 16,800, B4 400) and ≥ 100 bits at the stated
  Q.
- (P1) `MaskImageOn Good` proved (T2: structured mask family, Ψ_ch,
  containment (i′) and (ii′) under D15) and `hvzk_stat` with the 21/|K_α|
  term.
- (P2) ZF1: ZK_FS from HVZK in the adopted ROM definition (privacy LOG,
  "Adopted ZK_FS definition and explicit ZF1 composition"), with every ledger
  term (seed, salt, commit, algebraic bad, FS conflict, sampler abort, source)
  either proved or carried as an explicit named assumption with its value.
- (P3) Abort accounting at the model level: every honest-prover abort or
  retry event is a function of statement and challenges alone, or its
  witness dependence is bounded by a stated mass (ZR1, ZR2 masses), so that
  visible aborts do not leak.
Source refinement (G14, G18, ZR1–ZR3) is proved against the **deployed**
verifier and prover after optimisation, not against the reference; the fact
G_ref certifies is about the protocol.

**After G_ref: §8 in this order, each step Lean-first (statement, ledger,
replay), then Rust built to it, then exact kernel work with equality gates.**
1. §8 step 8: κ, τ in K (ledger re-evaluation only). V2's E×K weighting and
   its remaining E×E become K arithmetic.
2. §8 step 2: relation rounds 1–3 in place of V2's direct 1024-length dot
   (three degree-6 rounds, +18/|E|; V7 analogue in the tree). This is the
   step that removes V2's size.
3. §8 step 1: ρ-batch the 22 query equations into the relation (+22/|E|,
   `badCombinedChallenges_card`).
4. §8 step 3: eight-way Merkle (proved, R552). §8 step 4: two-swap order.
5. §8 step 6: channel fold (`quadratic_dot_product`). §8 step 5 last and
   only with its joint-list argument (the note's "not routine").
Lead estimate after steps 1–5 above, on R-E3's measurement: Semantic ≈ 0.7M,
ChordClaims ≈ 0.3M, Merkle ≈ 0.25M, V1 ≈ 0.4M, V2 ≈ 0.3M, total ≈ 2M. That
is below the measured 19.3M by an order of magnitude and still above 1.4M.
Closing the last factor needs a further parameter step (fold count, final
length, or the field of α₀ and F), designed and ledgered as a §8 step 9 when
the measured numbers after step 2 are in. **One transaction is not yet shown
reachable; this sequence is how it is found out, re-estimating after each
step.**

**Running now.** T1 (Lean; the only Lean job). R-E4 (Rust A) continues: it is
byte-preserving kernel work gated against the retained reference path, uses
no Lean capacity and incurs no proof debt; it is held only if the user says
so. T2 is specified when T1 lands; ZF1 after T2.

## Lead decision after user direction (2026-10-09, later): cost probe P1 of R0 + §8 before further Lean beyond T1

**Direction (user).** "We can't go from single tx to 10s of tx." v7 is one
transaction (≈ 1.08M CU, grinding, audited PCS argument, no full-view
privacy). If the compressed R0 cannot reach one transaction, R0 is the wrong
bet. This must be found out before further Lean spend, not after.

**Decision.** T1 continues (already launched; needed on every continuing
path). **No T2 or ZF1 is issued until P1 reports.** R-E4 is folded into P1 as
its first configuration. P1 is a **cost probe**: unproved Rust implementing
R0 with §8 steps applied, with a matching probe prover so the verifier runs
real arithmetic on real proofs; it lives beside the reference, never replaces
it, and makes no soundness or privacy claim. Its output is one table: for each
configuration, native acceptance, SBF validity (stack, heap), DIAGNOSTIC CU
per phase, and total. The decision rule: if no configuration fits
≤ 1,400,000 (target ≤ 1,300,000), R0 stops and v7 stands; if one fits, its
§8 steps are what T2-onward and the ledger prove, in that order.

Configurations (cumulative; measure each):
- C0: R-E3 + the exact savings (subfield chord coefficients, tensor builder,
  Karatsuba, K inversions in V1, M1 semantic kernels). Byte-preserving;
  equality-gated against the R-E3 path.
- C1: §8 step 8 — κ, τ sampled in K (ledger: arithmetic).
- C2: §8 step 2 — relation rounds 1–3 replacing V2's 1024-length dot (three
  degree-6 rounds; prover sends round polynomials; v7 analogue).
- C3: §8 step 1 — ρ-batched query equations injected into the relation (v7
  analogue; the 22 V1 checks and the 22 final-message evaluations collapse).
- C4: §8 step 3 — eight-way Merkle (proved R552), and step 4 two-swap order
  if it changes cost.
- C5 (what-ifs for a §8 step 9, each separately on top of C4): a second
  4-to-1 fold with a 64-coefficient final message; α₀ and F in K; both.
Each configuration: generated honest proofs for both fixtures, native
acceptance, the existing rejection corpus adapted where the wire changes,
SBF build with zero reachable stack diagnostics, heap ≤ 256 KiB, acceptance
runs at 1.4M, DIAGNOSTIC per-phase CU. Report per-phase and total for all
configurations in one table, with the proof size and the number of E, K and
F multiplications per phase.

**What P1 is not.** Not the reference, not merged into `r0/onchain.rs` or the
prover, not evidence of soundness or privacy for any configuration, not a
decision about which steps are adopted. Those are the lead's, from §8, after
the numbers.

## Lead acceptance of R-E4 (= P1 configuration C0): 15.08M CU measured; probe re-ordered as P1′ (2026-10-09)

**Verdict: accepted.** `codex/r0-e2e-re4-20261009` has six commits
(`3a2800bf8`, `589617d1d`, `61f27bf21`, `f4e1d419b`, `52df8fc21`, `87377ca78`;
the report named only the head), landed on `v8-reference` as
`ce0eeccca … 16ada04e4`. Report: `results/r0-e2e-20261009/REPORT-4.md`.

**Measured, DIAGNOSTIC at 200M, transfer (withdrawal in brackets for totals):**

| Stage | Semantic | ChordClaims | Merkle ×22 | V1 ×22 | V2 | Total | Δ |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| R-E3 | 2,693,892 | 1,008,549 | 641,001 | 3,476,468 | 11,507,624 | 19,335,682 | — |
| S1 subfield chord | 2,693,892 | 1,008,644 | 641,001 | 3,047,614 | 9,082,171 | 16,481,470 | −2,854,212 |
| S2 tensor v−r | 2,693,892 | 1,008,644 | 641,001 | 3,047,614 | 8,300,336 | 15,699,635 | −781,835 |
| S3 outer Karatsuba | 2,647,122 | 968,572 | 641,001 | 3,010,106 | 8,137,088 | 15,412,037 | −287,598 |
| **S4 V2 transpose (selected)** | 2,647,122 | 968,572 | 641,001 | 3,010,106 | 7,803,350 | **15,078,299** (15,070,869) | −333,738 |
| S5d R91 (deselected) | 3,400,620 | 1,226,117 | 641,001 | 4,019,047 | 12,743,485 | 22,038,418 | +6,960,119 |

Per fibre at S4: Merkle ≈ 30K, V1 ≈ 137K. Heap 131,032 B. Zero reachable stack
diagnostics. Both fixtures and the 1,894-case corpus byte-identical to R-E3.
Acceptance runs still exhaust 1.4M inside Semantic.

**What I checked.** `subfield_line` asserts the high QM31 limb of a, b, c is
zero (it never fires: z0, z1 are `from_qm31` embeddings and the secant is a
rational function of their coordinates; `WrongField` is kept as a defensive
error). `quotient_weights`/`chord_weights` use `mul_qm31`; `chord_weights` is
the exact transpose (C applied to G = D·F in channel order [0,3,2,1]; the τ
image rows are taken from G before the in-place map, matching the original
order in which τ rows were added after Cᵀ). `eq_tensor` computes `r = v·x`,
`ℓ = v − r`. Karatsuba replaces the outer layer of `WideExact::mul`; the
schoolbook `mul_re3` is frozen under the native-only `r0-e4-reference` feature
and its thread-local guard is `cfg`'d out of SBF. R91 sits behind the
default-off `r0-r91-audit` feature in the core, statement, prover and verifier
manifests. The native differential `r0_verify_re3` compares phase order, exact
errors, query sets and passive field-byte traces (circle points, challenges,
polynomial, powers, interpolant, every V1 fibre result, V1/V2 sides). The
op-counter matches every counted primitive on both fixtures. EMul calibrated
1,466.6 → 1,312.2 CU (N = 128).

**Estimate vs measurement.** My exact-savings estimate was 5–6M; measured
4.26M. Chord 2.85M (est. ≈ 2.67M) and tensor 0.78M (est. 0.9M) held. Karatsuba
0.29M (est. 0.5–0.7M): only 1,039 E×E remain in V2 after S1. The V2 reorder
saved 0.33M against the "≈ 6.5–7M" V2 figure in the R-E4 spec; that figure
assumed the dense form's E×K/E×F mix and is superseded by the worker's
four-schedule count ledger (`re4/V2-ORDERS.md`). Semantic kernels: R60 is
already the `M31::inv` chain; R218 has no matching call shape in R0's semantic
verifier; R91 regresses by 7M on SBF because the raw-input fallbacks need
`inline(never)` boundaries to stay within branch displacement. The spec's
"≥ 1M semantic recovery" line is withdrawn; the negative result is accepted as
reported.

**Process correction (evidence size).** R-E4 committed 46.6 MB under `re4/`,
including six ELF images, an unstripped ELF, `.text` dumps and six 3.7 MB
disassemblies (R-E3 set the precedent at 9.5 MB). Accepted this once. **Rule
from P1′ on:** no ELF/`.so`/`.text`/disassembly files in commits; record each
artifact's SHA-256 and size in the artifact manifest and keep the files on the
build host under the results path; commit JSON/MD/log evidence only; one
stack-audit JSON per configuration.

**What the measured base says about one transaction.** Semantic alone,
2,647,122 CU, is 1.9× the 1.4M budget. M1 (`results/v8-state-only-cu-20261009`,
the same state-only rows in QM31, a 24-round sumcheck) measured
transcript/sumcheck replay 140,757 + terminal incl. mask 286,713 = **427,470 CU**
for its semantic work; R0's semantic phase is **6.2×** that. R0 adds mask lanes
16–25, η, the 32-round schedule, three point-claim evaluations and 29-lane
claims, which do not account for 6×; the remainder is overhead to be located
(wire decoding and canonical checks of E values, transcript hashing of a ~95 KB
proof, heap). ChordClaims at 968,572 for `prepare()` is likewise about four
times its priced arithmetic (interpolant 58 E×E, `claim` 87 E×E, chord pair,
squeezes, query sampling). Per fibre, V1 measures 137K against roughly 85K of
priced arithmetic. **Updated lead estimate after §8 on the measured base
(estimate, not a result):** Semantic → 0.5M if M1-class overhead is reached;
ChordClaims → 0.2M; Merkle 8-way → 0.45M; V1 with ρ-batch → 0.5M (the
22×4×29 opened-value products, ≈ 0.37M, stay unless steps 5/6 reduce lanes);
V2 by relation rounds → 0.6M (F at a point 256 E×K, the inactive indicator at a
point ≈ 890 K-mults unless structured, eq 30 K-mults, chord weight at a point
structured). Total ≈ 2.25M. One transaction therefore needs the step-9
what-ifs **and** semantic overhead at M1 level. P1′ tests exactly this.

**P1′ (revision of P1; Rust A).** Base: the `origin/v8-reference` head
carrying this section. Branch `codex/r0-cost-probe-p1-20261009`; report
`results/r0-cost-probe-20261009/REPORT-P1.md`. Decision rule, labelling,
caps and gates as in the P1 section above; changes:

1. **C0 := R-E4 S4** (15,078,299 / 15,070,869). Not re-measured.
2. **B — breakdown, reported alone first.** Fine-grained DIAGNOSTIC markers
   inside Semantic (parse + canonical checks; transcript absorb/squeeze; the 25
   round checks; the 10 α-round polynomial evaluations; terminal incl. mask;
   point/extra-claim handling; handoff), inside `prepare` (transcript, data
   copy, `validate_points`, interpolant, chord pair, `claim_prime`, query
   sampling), one fibre's V1 (value decode, four dots, four inversions, fold,
   `final_encoder`) and V2 (G, `chord_weights`, indicator sum, 3 × tensor +
   pairing, images). One table against M1's phases; name where the ≈ 2.2M
   semantic excess and ≈ 0.77M prepare excess sit. No optimisation in B.
3. **C0′ — byte-preserving overhead removal** guided by B, with R-E4's
   equality gates (both fixtures, 1,894 rejections, field-byte traces); no
   wire, transcript, check-order or predicate change. Per-change table.
4. **C2** §8 step 2 (relation rounds replacing V2's dot) → **C3** §8 step 1
   (ρ-batched query equations) → **C4** §8 step 3 (eight-way Merkle; step 4
   two-swap if cost-relevant) → **C5** what-ifs on C4: (a) second 4-to-1 fold
   with a 64-coefficient final message; (b) α₀ and F in K; (c) both.
5. **C1 (κ, τ in K) is dropped from measurement.** After S4, κ enters V2 as
   three E×E products (`k[p+1].mul(pairing)`) plus its powers, τ as two; with
   `claim_prime` the whole κ/τ footprint is under 30K CU by inspection. §8
   step 8 stays a ledger decision, not a cost item.
6. Report each configuration as it completes; the lead may stop after any.
   Evidence rule above applies.

**R-H is held** with T2/ZF1 until P1′ reports (privacy LOG, D16).

## Lead review of P1 (pre-prime) and P1′ (B): the probe closes; R0 does not reach one transaction (2026-10-10)

Two workers ran in parallel on the same branch name: one completed the
original P1 (C0–C4, stopped at C5(b)) from `f1e5ca9de`, the other ran P1′ from
`bedd04207` and stopped at B's reconciliation gate. Both branches are pushed
(`codex/r0-cost-probe-p1-pre-prime-20261010` @ `24db293e8`;
`codex/r0-cost-probe-p1-20261009` @ `70544d55a`); the two reports are copied
to `results/r0-cost-probe-20261009/`. Neither is merged into reference paths.

**P1′ B — accepted as the breakdown measurement.** The stop rule I wrote
("markers must sum to the S4 phase totals within logging cost") was read as
exact; the residuals after calibrated logging are Semantic −363, ChordClaims
+175, Merkle −350, V1 +18,066 (0.6 % of the phase; 779 CU per fibre of guard
code), V2 −1,537 CU. A tolerance of 1 % per phase was the intent; B passes it.
The 14 fixed-challenge rejection cases that still call reference helpers do
not affect B (B changes no arithmetic). B's figures (transfer, raw, including
≈38K of marker cost):

| Where | CU | Note |
| --- | ---: | --- |
| Semantic: rows 0–14 sampling/orchestration | 817,145 | `qm31_sample`: 256-bit binary long division + eight base-P divisions per sample |
| Semantic: ten α samplers/orchestration | 552,037 | same sampler |
| Semantic: ten α-round polynomial evaluations | 393,528 | evaluated in E; the data is K-valued |
| Semantic: terminal incl. mask | 641,100 | M1: 286,713 |
| Semantic: claims/handoff/parse/hash/checks | 281,265 | hashing itself only 24,400 |
| Prepare: opening parse + canonical | 231,439 | |
| Prepare: z0/z1/batch/α transcript + samplers | 325,503 | same sampler |
| Prepare: `claim_prime` | 217,290 | 145 E×E on K-valued claims |
| V1 per fibre: value decode | 33,084 | 116 `E::from_le_bytes` for M31/K data |
| V1 per fibre: `final_encoder` | 64,532 | 22 of these; ρ-batching removes 21 |
| V2: G / chord_weights / tensor / pairing | 1,047,619 / 3,163,882 / 1,090,356 / 2,367,456 | structural |

**P1 pre-prime — accepted as computation; its baseline is not comparable.**
Its C0 (22.5M) includes R91, which R-E4 measured at +7M, and excludes the V2
transpose, so its absolute totals and its C1 saving (−5.2M, mostly R91 and
pre-transpose κ products) do not transfer to S4. Four facts do transfer:
(1) **R0's Merkle is already eight-way** (`Path = [[Digest; 7]; 6]`), so §8
step 3 is implemented and C4 is a no-op; (2) **relation rounds added on top of
the explicit 1,024-entry weight construction cost more, not less** (V2 +0.83M),
so §8 step 2 saves nothing without a compact evaluator of the weight functional
at a point — which no one has designed for the natural-basis chord map; that
design is §8 steps 4–6 (two-swap transport, channel fold, sparse G), the
"not routine" ones; (3) **ρ-batching (§8 step 1) works as expected**: it
removes 21 of the 22 final-message evaluations, ≈ −1.35M on S4; (4) **F in K
is not a parameter change**: the batched word Σ γ^c W_c is E-valued because
γ ∈ E, so F ∈ K needs γ ∈ K, and then the γ collision term becomes
336,869,026,622,539/(2¹²⁴ − 1) ≈ 2⁻⁷⁵·⁷, i.e. ≈ 75-bit soundness. C5(b) is
closed as a field change, not a what-if.

**Where the numbers lead.** From S4 = 15,078,299:

| Step | Kind | Estimated total after |
| --- | --- | ---: |
| C0′ byte-preserving: sampler rewrite (same outputs), M31/K decodes, K arithmetic on K-valued semantic data, E×K in `claim_prime` | implementation | ≈ 12.3M |
| C3 ρ-batched queries | §8 step 1 | ≈ 11.0M |
| V2 with a compact evaluator, if one exists for the natural basis (my MLE sketch: ≈ 4–5M for V2) | §8 steps 2, 4–6 | ≈ 8M |

Independent anchor: M1 (`results/v8-state-only-cu-20261009`) spent 557K on its
whole PCS (relation 150K, Merkle 176K, queries 231K) in K at 16 queries.
R0's opening layer in E at 22 queries and 29 lanes costs at least
557K × 22/16 × 29/25 × (2 to 3 for E over K) ≈ 1.8–2.7M even at M1's
implementation quality, plus ≈ 0.45M semantic and ≈ 0.3M prepare at the same
quality: **≈ 2.5–3.2M is R0's floor before any proof work, 1.8–2.3× the
budget.** Moving the opening field to K would cost the 100-bit target
(≈ 75 bits, above). Recovering the old v8's 1.21M needs its verifier shape
(four folds, channel fold, sparse G, QM31 opening field) — a different protocol
with its own soundness ledger, not an optimisation of R0.

**Verdict under the decision rule (PLAN "Lead decision … cost probe P1").**
No measured configuration is ≤ 1.4M; the best measured is S4 at 15.08M. The
unmeasured steps that remain byte-preserving or routine reach ≈ 11M; the
structural steps cannot take R0 below ≈ 2.5M on any estimate. **R0 stops as
the deployment target; v7 stands.** The probe is closed: no C0′, C2–C5, no
further Rust job is issued. The lead asks the user to confirm.

**What R0 remains.** A protocol with a proved 100-bit soundness model
(`combined_fiat_shamir_masked`, T1 constants) and a privacy model one theorem
from closure (`MaskImageOn Good`; T2a issued today on the user's direction;
T2b route in the privacy LOG D17.3). That is research value, not a deployment
path. R-H, ZF1 and the refinement block stay held. If a one-transaction proved
design is wanted later, it starts from the old v8 verifier shape as a new
protocol (call it R1) with R0's semantic layer, mask and proof techniques
reused, and a soundness ledger written before any Rust.

**Process notes.** (a) Superseding a prompt in flight needs an explicit stop
to the old session; the two parallel runs cost one full probe. (b) Stop rules
must carry tolerances. (c) The pre-prime branch committed ELF/stack binaries
under the original P1 text; the P1′ branch followed the new rule. Both stay on
their branches.

## Lead decision after user direction (2026-10-10): two transactions accepted if R1 fits; R1 outline; fit gate = Z5 + P2

**User direction.** Work-normalised security (grinding) is rejected: the
per-query error must be ≤ 2⁻¹⁰⁰ as a probability, with no credit for prover
hash work. **Two transactions are acceptable if the verifier can be made to
fit.** R0 stays stopped as a deployment target (previous section); its proofs
are the base of the successor.

**Why the field is fixed.** Only two challenges fail 100 bits over QM31, and
both are proved degree caps that do not depend on the field: the lane-batching
challenge γ (bad set ≤ 336,869,026,605,739 ≈ 2⁴⁸·³, F1,
`width29_bad_response_challenges_card_le`) and the fold challenge (≤
9,396,508,281,246 ≈ 2⁴³·¹, F2, `goodChallenges_card_le_of_no_jointAgreement`).
Over QM31 these are 2⁻⁷⁵·⁷ and 2⁻⁸⁰·⁹; both need a field ≥ 2¹⁴⁸, hence E for
γ and every fold challenge, hence an E-valued batched word, fold, final
message and per-query arithmetic. Everything else (semantic α rows, η, z0, z1,
κ, τ, the opening polynomial, the semantic sumcheck's degree-27 rounds) is
already ≤ 2⁻¹⁰⁵ over QM31.

**R1 outline (the protocol to be ledgered; not yet a spec).**
- Semantic layer, mask, η row, Libra tail, 29 lanes, the proved semantic
  sumcheck: unchanged from R0.
- Commitment: unchanged from R0 (29 lanes, domain 2²⁰, fibres of 4, two
  eight-way Merkle trees); leaves packed by lane field (M31 lanes 4 bytes).
- Opening layer: **no chord quotient.** The batched trace f_γ = Σ_l γ^l W_l
  (γ ∈ E) is folded directly. Every claim on it is a linear functional with
  product-form weights over the base-4 digits of the coefficient index: the
  three point claims (eq tensors at α_j ∈ K), the two OOD claims (natural-basis
  values N_j(z_i) at z_i ∈ K, which the N_{4k+t} recurrence makes a product over
  digits), the inactive sum (0/1 weight; its dual fold is sums of challenge
  powers) and the Libra row (56 K entries). They are batched with powers of
  κ ∈ E and verified through **two 4-to-1 folds** (α₀, α₁ ∈ E), each with R0's
  degree-6 relation polynomial and boundary check, ending in a 64-coefficient
  final message whose pairing with the dual-folded weights costs ≈ 7 × 64 E×K.
  The 22 queries follow the fibre chain through both oracles; the 22
  final-message evaluations are ρ-batched into one.
- Soundness over E: γ term 2⁻²⁰⁰, two fold terms 2⁻²⁰⁵ each, OOD
  list-to-unique at z ∈ K ≈ 100·1024/2¹²⁴ ≈ 2⁻¹⁰⁷, query term at rate 2⁻¹⁰ with
  22 queries ≈ 2⁻¹⁰⁵ (the second round's proximity at domain 2¹⁶, same rate,
  needs its own instance of F2). Target per-query ≤ 2⁻¹⁰⁰ without grinding.
- Two transactions: tx1 = parse, semantic, prepare, first k queries, write a
  checkpoint (transcript state, ρ accumulator, counters); tx2 = remaining
  queries, relation rounds, final check. k chosen to balance.

**The crux: the transport.** R-E4's V2 is 7.8M, of which the chord map is
3.2M and **3.5M is the point-claim weights pulled through the D13 transport π**
(tensor 1.09M + pairing 2.37M): π is the identity with 89 pad rows moved to
coefficients 0–88 (`transport.rs`), so eq(α, π⁻¹ j) has no product form and
must be materialised and paired at length 1,024 in every design. R1 fits only
if π is **digit-structured**: a permutation of the five base-4 digit positions
composed with per-digit permutations of {0,1,2,3}. Such a π keeps every weight
in product form (eq, N_j(z), the Libra row) and the dual fold then costs O(1)
per constraint. Whether a digit-structured π has the C1 full-rank property
that D13 was reinstated for (rank 112 per semantic column on both fibre sets,
Z4a/Z4c) is a numerical question the existing Z4 probe answers. If none does,
R1's relation is ≥ 3.5M more and two transactions do not fit either.

**Lead estimate for R1 with a digit-structured π (estimate, not a result):**

| Phase | CU | Basis |
| --- | ---: | --- |
| Semantic (sampler and K fixes) | 0.45M | M1 anchor 427K |
| Prepare / transcript | 0.25M | B's intervals minus sampler and parse waste |
| Merkle, 22 queries, two oracles, packed leaves | 0.22M | 2 × 2.9K paths + 1.4K leaves + folded oracle ≈ 10K per query |
| Per-query arithmetic (29-lane dots, two folds; no inversions) | 0.77M | ≈ 35K per query |
| Relation rounds and final pairing (final64, 7 constraints) | 0.32M | 2 × ≈ 10K + 448 E×K |
| Checkpoint write/read | 0.05M | |
| **Total** | **≈ 2.05M** | ≈ 1.0M per transaction at an even split |

**Fit gate, two jobs, both unproved probes, issued now in parallel:**

- **Z5 (privacy Codex, computation only).** On the Z4c probe, test
  digit-structured transports for the D13 rank property. Candidate family:
  π(r) = Σ_d σ_d(digit_{τ(d)}(r))·4^d with τ a permutation of the five digit
  positions and σ_d ∈ S₄ per digit. Order: all 120 τ with σ = id; then τ × σ
  on the lowest coefficient digit (2,880); then up to 100,000 random (τ, σ).
  Criterion per candidate: C1 rank 112 for all 16 semantic columns on the
  random 22-fibre set and on {0,…,21}, with the fourth weight row, exactly as
  Z4c's C1 test. Report every passing candidate; for the first passing one run
  Z4c's full gate (silent rank, (i′), (ii′), 100 targets) with that π. Also
  report the identity π and D13's π as controls. Branch
  `codex/z5-digit-transport-20261010`, `z4/FINDINGS-Z5.md`, standard caps and
  evidence, no Lean, no production Rust.
- **P2 (Rust A, cost pre-check).** Build R1's verifier shape as a probe from
  the R0 Rust (probe crate, probe prover, never the reference paths): semantic
  layer with the sampler rewrite and K arithmetic on K-valued data
  (byte-identical outputs, gated against S4's semantic phase), commitment as
  R0 with packed leaves, the opening layer above with two folds and final64,
  ρ-batched final evaluations, OOD-as-weights, no quotient. Two weight
  variants: **S** (a digit-structured π, placeholder τ = digit reversal,
  σ = id; cost does not depend on which structured π) and **D** (the current
  D13 π with materialised eq tensors). Two-transaction split with a checkpoint
  account; find k; measure both transactions on SBF: acceptance at 1.4M each
  (×5), DIAGNOSTIC per-phase CU, heap ≤ 256 KiB, zero reachable stack
  diagnostics, proof bytes. Native acceptance on both fixtures; a dense native
  evaluator of the same relation as a self-consistency oracle; a small mutation
  corpus (≥ 200 cases: every message type) must reject. One table: phase ×
  variant × transaction. Report S first, then D. Branch
  `codex/r1-precheck-p2-20261010`, `results/r1-precheck-20261010/REPORT-P2.md`,
  evidence rule (no binaries), labelled unproved, no claim language.

**Decision rule.** R1 proceeds to the ledger only if Z5 finds a passing
digit-structured π **and** P2's variant S fits two transactions with ≥ 0.2M
headroom in each. Then: R1_SOUNDNESS ledger (lead), then Lean (reuse map:
semantic/mask proofs, width-29 and degree-three correlated agreement, FS
framework, fold lemmas, privacy clause (i′); new: two-fold binding without the
quotient, OOD-as-constraint collision set, second F2 instance at 2¹⁶, privacy
(ii′)'s PCS half, the structured π in Lean), then Rust to the proved spec. If
either gate fails, the accurate statement is that a non-work-normalised
100-bit proved and private verifier does not fit two transactions with the
theorems we have, and v7 stands.

### P2 clarification — the Libra row in the probe (2026-10-10)

The base Rust has no D14 content (R-H is held). The probe implements the Lean
form from T1 (`R0/OpeningDefinitions.lean`, `R0P/SemView.lean`,
`R0P/MaskValue.lean`), as protocol content on top of the gated semantic
rewrites:

- Weight, coefficient-indexed, no transport applied:
  `w_extra(j) = α₈^j` for `j < 28`, `α₉^(j−28)` for `28 ≤ j < 56`, `0` otherwise,
  with α₈, α₉ the ninth and tenth semantic sumcheck challenges (K-valued).
  Sparse: 56 entries; its dual fold has 14 nonzero entries after the first
  fold and 4 after the second. No product form is needed.
- Per-lane claim: `extraClaims_l = Σ_{j<56} w_extra(j) · m_l(j)`, `m_l` the
  committed coefficient vector of lane l (coefficient order, i.e. after the
  transport), for all 29 lanes; K-valued.
- As a functional of the batched coefficient vector `f_j = Σ_l γ^l m_l(j)`:
  `Σ_j w_extra(j) f_j = Σ_l γ^l extraClaims_l` (`width29Batch extraClaims γ`),
  entering the κ-batch with weight κ⁴ (the three point claims carry κ¹…κ³, the
  inactive sum 1; for the probe the two OOD constraints take κ⁵, κ⁶).
- Honest prover: lane 28 coefficient cells 0–27 hold h₈ and 28–55 hold h₉,
  two degree-27 univariates with uniformly random K coefficients drawn with the
  other mask samples; the masked terminal gains `+ extraClaims_28 = h₈(α₈) + h₉(α₉)`;
  the mask-sum claim gains `2⁹·(h₈(0)+h₈(1)+h₉(0)+h₉(1))`; the ten round
  polynomials need no separate handling when they are interpolated from the
  terminal over the hypercube (Z4c's table is what falls out).
- Disclosure: the 29 extra claims travel in the same message as the three
  point-claim rows, before z0 is squeezed, absorbed as they are (D14′ item 4).
- Gate order: the sampler rewrite and the K-arithmetic rewrite are gated
  byte-identical against S4 on the **unmodified** semantic layer first; the
  D14 content is then added as a protocol change and is covered by the dense
  native oracle, honest acceptance and the mutation corpus, not by byte
  identity with S4.

### Lead note after the Lean reuse inventory (2026-10-11): fold count is decided by P2, one fold preferred

`docs/research/v8-r1-20261011/REUSE-INVENTORY.md` classifies all 212 Lean
modules for R1: 120 reuse as they are (the whole semantic layer and mask, the
GS/Hensel machinery, the initial-code chain F1/F3, the FS/duplex lemmas, the
abstract ZK laws), 39 re-instance with new parameters, 12 rewrite, 5 retire
(the four Chord modules and `R0Z/QuotientImage`), and 32 are reusable for the
first fold but would need a second copy for a second fold. Three findings
change the R1 outline:

1. **A second fold is cheap on-chain and expensive in Lean.** The proved
   final-code chain (`Wide/Final*`, `Terminal`, `MatchedInstances`,
   `GRSConversion`, `Interpolation`, `FactorBudgets`, F4 in `R0/Fold`, F5 in
   `R0/Round`) is hard-wired to one 4-to-1 fold landing in the 256-coefficient
   code on 2¹⁸ points with threshold 9557 and `foldChallengeCap`. Two folds
   need a new instance of all of it for a 64-coefficient code on 2¹⁶ points
   (new encoder, GRS conversion, interpolation budget, cap, and an unverified
   Hensel Y-degree < 113 condition) and a fold identity on the line domain
   that has no Lean analogue in these trees. That is weeks of Lean for ≈ 0.6M
   CU: with one fold the final pairing costs ≈ 0.86M instead of ≈ 0.3M
   (3 point claims 3 × 256 E×K, 2 OOD claims 2 × 256 E×K, the inactive sum
   almost free because under π_R1 the active rows are a function of the top
   two coefficient digits, the Libra row 14 E×K after the fold). One-fold R1
   estimate ≈ 2.35M, i.e. ≈ 1.2M per transaction with ≈ 0.2M headroom each:
   at the rule's threshold. **P2 measures both: variant S1 = one fold + final256
   (R0's proved fold), variant S2 = two folds + final64. One fold is chosen if
   S1 fits the rule; two folds only if S1 does not and S2 does.**
2. **OOD points stay circle points over K** (z0, z1 sampled as now), so
   `R0C/Circle*`, `R0P/CircleSampler` and `ChordGeometry.Point` are reused; the
   OOD functional is `evalMessage` salvaged from `R0/Chord` (the natural-basis
   values N_j(z), product form over digits). The chord conditions (rational /
   equal points) are replaced by one OOD list-to-unique collision row: two
   distinct list elements agree at z for at most 1,024 circle points, so with
   list ≤ 100 the bad set is ≤ 4,950 × 1,024 ≈ 2²²·³, i.e. ≈ 2⁻¹⁰¹·⁷ per OOD
   round over K. Both OOD rounds are kept.
3. **Queries stay uniform 22-subsets of the 2¹⁸ fibres** with one fold
   (`QueryLaw`, `Q22Law`, `QuerySampler` reuse). The ρ-batch challenge is
   sampled after the query set, so the FS round list becomes γ, κ, α₀, S, ρ
   (τ is gone, ρ is new): 33 rounds; the `MaskDuplex*` chain is re-instanced
   mechanically.

Every transport use takes π as a parameter except `R0Z/HonestView.D13Order`,
so π_R1 (D18) plugs in. Over QM31 only the γ and fold terms fall short of 100
bits (75.74 and 80.90); all semantic terms are ≥ 105.27 bits over |K|; the
query term (105.14) is field-independent — consistent with the R1 outline.

## Lead review of P2 (2026-10-11): R1 does not fit two transactions; the fit gate fails; v7 stands

**Accepted as computation.** `codex/r1-precheck-p2-20261010` @ `d2197e355`
(pushed; report copied to `results/r1-precheck-20261010/REPORT-P2.md`; no
binaries committed). Gates: the sampler and K-arithmetic rewrites were
byte-identical to S4 on the unmodified semantic layer before the D14 content
was added; every emitted challenge, weight and check value agrees bitwise with
a dense native evaluator (20,465 values per fixture for S1, 10,699 for S2/D);
1,422 / 898 mutation cases reject; zero reachable stack diagnostics; heap
≤ 56,148 B; caps 4G/6G/swap 0, none raised. One retention defect disclosed:
S1's native-gate executable was overwritten before archival (its result JSON,
trace hash, corpus, logs and exact source are retained); it does not affect
the CU figures. The worker's round count (32 for S1, 33 for S2) is right and
my "33 FS rounds" note was off by one for S1.

**Measured, DIAGNOSTIC, worst fixture (CU):**

| Variant | Split k | Tx1 | Tx2 | Pair total | Rule (≤ 1.2M each) |
| --- | ---: | ---: | ---: | ---: | --- |
| S1 one fold, final256, π_R1 | 14 | 3,331,310 | 3,439,672 | 6.77M | fails |
| S2 two folds, final64, π_R1 | 10 | 2,441,407 | 2,414,242 | 4.85M | fails |
| D two folds, D13 π | 22 | 3,542,936 | 5,716,002 | 9.26M | fails |

All 60 capped attempts at 1.4M failed. Per phase (S2, transfer): parse 57K +
36K; semantic 903K; prepare 489K; checkpoint 68K + 115K; Merkle 100K + 120K;
query folds and ρ accumulation 822K + 984K (≈ 82K per query); relation rounds
and pairing 1,059K; final pairing 94K.

**Reading.** The probe is a first-cut implementation and runs about 2× my
arithmetic-floor estimate in every phase (semantic 0.90M vs 0.45M, prepare
0.49M vs 0.25M, per-query 82K vs 35K, relation 1.06M vs 0.30M, checkpoint
0.19M vs 0.05M); that factor has been the pattern of every probe in this
programme and I no longer discount it. But the verdict does not rest on it.
Two structural facts close the question:

1. **Semantic plus prepare alone exceed one transaction** (1.39M measured;
   ≈ 1.0M at the floor, since the terminal in K ≈ 0.30M matches M1's 287K and
   the four claim rows, handoff and α evaluations are R0 content, not waste).
   Transaction 1 therefore carries no query before it is nearly full.
2. **The design's arithmetic floor sits on the two-transaction budget line.**
   Floor: semantic 0.75M + prepare 0.25M + parse 0.06M + checkpoints 0.17M +
   Merkle 0.22M + 22 queries × 35K + relation 0.30M + final 0.10M ≈ 2.6M,
   i.e. ≈ 1.3M per transaction with zero implementation overhead. The rule
   asks for ≤ 1.2M each. No implementation reaches below its own arithmetic
   floor.

**Verdict under the gate (PLAN, 2026-10-10 decision).** Z5 passed; P2 fails:
R1 does not fit two transactions. **R1 does not proceed to the ledger; v7
stands.** No further Rust job is issued. For the record: as measured, R1
needs four transactions (≈ 4.85M / 1.2M); with an optimisation programme of
the old v8's kind (R17–R91, months) it might reach three; two is excluded by
the floor, one was excluded by the field. The D variant confirms D18's point
by contrast: the D13 transport alone adds ≈ 4.4M to the relation phase.

**What stands.** R0: a proved 100-bit soundness model and a privacy model one
theorem from closure, both with research value and no deployment path. The
old v8 verifier shape remains the only measured one-transaction design, and
its security is work-normalised and unproved. The Lean privacy work in flight
(T2b-1 after Z6) continues only if the user wants it as research.

## Lead review of the `codex/100bit-spend-path-20261013` checkpoint (2026-10-13); decision: the P2 verdict is amended, the fit gate is re-stated, and R1 becomes a live candidate under gate G_R1

**What was reviewed.** Worktree `.worktrees/100bit-spend-path`, branch
`codex/100bit-spend-path-20261013` at `628054cd4` (base `774295764`, one
checkpoint commit plus live uncommitted edits in `crates/aspis-r1-cost-probe`,
`tools/r1-cost-probe` and `programs/r1-cost-probe`; two Codex sessions
active). Read in full: `CHECKPOINT.md`, `SECURITY-PATH.md`,
`SECOND-FOLD-LIFT.md`, `TWO-ROUND-BINDING.md`, `PRIVACY-RANK-PATH.md`,
`RESULTS-FIT.md`, `security-ledger.json` + `security_ledger.py`, the six Lean
files and their axiom receipts, `evidence/pool-v0`, `evidence/pool-v2`,
`evidence/authenticated-tx2-gate-20261013`; and the verifier diff of
`crates/aspis-r1-cost-probe` against the P2 head `d2197e355` (26 files,
+2,628/−335; the removed lines are the second transaction's strict per-record
parse checks, replaced by a checkpoint-bound authenticated digest).

**Accepted as computation.** The staged S2 verifier (D18 transport, two
folds, final 64 `WideExact` values, γ/κ/α₀/α₁ in `WideExact`, ρ in QM31)
measures, at the 1.4M cap, on the P2 fixtures:

| | P2 S2 (tx1 / tx2) | d18 verifier (whole tx) | with Pool adapter v2 |
|---|---:|---:|---:|
| Transfer CU | 2,441,407 / 2,411,848 | 1,331,566 / 1,282,345 | 1,342,707 / 1,374,664 |
| Withdrawal CU | 2,435,353 / 2,414,242 | 1,330,319 / 1,282,305 | 1,341,346 / 1,390,957 |

Five capped runs per transaction, dense-trace agreement, 832/1,164 mutation
rejections, zero reachable stack diagnostics, caps 4G/6G/swap 0, hashes
recorded. Pool lifecycle (sealing, authority, altered proof, wrong release,
stale lane, nullifier replay, injected CPI rollback) exercised on LiteSVM.
The 255-pair history rollover **exceeds the cap** (verifier exhausts
1,286,887 of 1,286,943 remaining CU; Pool 1,399,494 of 1,399,550).

**Correction of the P2 record.** My P2 review put the design's arithmetic
floor at ≈ 2.6M for the pair and concluded "two is excluded by the floor".
The pair now measures 2.61M: the floor estimate was right and the exclusion
was wrong, because it judged against our ≤ 1.2M-each rule with 0.2M headroom
rather than against the cap. Against the cap the ordinary case fits with
57K/25K headroom (transfer) and 59K/9K (withdrawal); against our rule it
fails; the rollover case fails outright. **The P2 verdict "R1 does not fit two
transactions" is withdrawn; "v7 stands" remains until gate G_R1 below closes.**
Nothing else in the P2 review changes: Z5 passed, the soundness bound is not
work-normalised, and the field choices (opening in `WideExact`, ρ in QM31)
are the ones the soundness caps require.

**What is not yet established, in the checkpoint's own words and mine.**
1. The ≈ 1.1M per transaction saved between P2 and the first named stage
   ("pairing") is not reconciled per phase anywhere; the stages are named,
   hashed and equivalence-tested, but no table in P2's format exists.
2. The authenticated-parser change removes strict parse checks from tx2
   (record lengths, tags, canonicality `echeck` of `WideExact` values, row
   order, trailing bytes, checkpoint header) in favour of a digest bound to
   the tx1 checkpoint. Mutations are rejected, but the covering argument —
   tx1's strict parse plus the digest implies every property tx2 relies on,
   including canonicality of values it then multiplies — is not written.
3. All CU figures use deterministic partial fixture masks; no run with full
   random masks is recorded for the SBF verifier.
4. Soundness is a proof design with small compiled lemmas (root bounds,
   field identities, arithmetic feasibility); the second-fold extraction,
   joint-list binding, both round comparisons, source correspondence and FS
   instantiation are open. The ledger's largest row is the existing q22
   envelope (≈ 2^-105.1) — the right shape, not yet a theorem for R1.
5. Privacy: the checkpoint found the same γ-in-QM31 modelling gap as the
   privacy LOG's D20′ and compensates with both K₄-valued pads G and D, as
   D20′.2 requires; its probe reaches silent rank 1,076 on the actual R1
   payload. The open theorems are the LOG's: spanning (T2b-2b), (ii′), an
   efficient simulator, the ROM reduction, aborts. The Rust verifier
   includes the Libra fourth row (D14), so R-H's content is present in R1.
6. The Pool adapter runs on a verifier release identity shared with the old
   path; a distinct R1 profile/release is required before any deployment.
7. Entropy: fixture entropy is insecure by design; secure entropy, salted
   leaves and durable nonce reservation are not integrated.

### Gate G_R1 (re-stated fit gate; replaces the 2026-10-10 fit rule)

R1 proceeds towards deployment only when all of the following hold, each
with receipts in P2's format (caps, hashes, five capped runs, mutation
corpus, dense-trace equivalence):

- **G_R1.1 Cost.** Whole-transaction CU, including the Pool adapter, for
  transfer and withdrawal at **≤ 1,300,000** per transaction (≥ 100K headroom
  at the 1.4M cap; the lead will accept ≥ 50K only with a written runtime-drift
  analysis covering compute pricing, syscall costs and adapter variance),
  measured with **full random masks**, and the **rollover case fits the same
  bound** or the history design is changed so that rollover is not part of a
  user's spend (a user decision; the plan's default is "must fit").
- **G_R1.2 Reconciliation.** A per-phase table (parse, semantic, prepare,
  checkpoint read/write, Merkle, query folds, relation rounds, final) for the
  selected ELF against P2's table, attributing every saving to a named stage
  and an equivalence test; any phase that disappeared must say where its
  work went.
- **G_R1.3 Authentication argument.** A written covering argument for the
  authenticated tx2 parser (what tx1 checks, what the digest binds, what tx2
  assumes), audited by the lead, plus a mutation corpus targeting exactly the
  removed checks (non-canonical limbs, row order, trailing bytes, header).
- **G_R1.4 Soundness ledger closed.** `R1_SOUNDNESS.md` (lead; see below)
  with every row either a compiled theorem at the R0 standard
  (`[propext, Classical.choice, Quot.sound]`, host receipts) or an explicitly
  retained assumption the user has accepted.
- **G_R1.5 Privacy closed** to the standard of the privacy LOG: `MaskImageOn
  Good₂` for the R1 payload, `ZK_FS` with the ledger term, an efficient
  simulator statement, and the ROM reduction (ZF1 series).
- **G_R1.6 Release and entropy.** Distinct R1 release identity; secure
  entropy, salted leaves and nonce reservation integrated; the fixture path
  removed from any deployable build.

### R1_SOUNDNESS ledger (lead deliverable, next)

Rows, each a stated obligation with its cap, field, and the theorem or
assumption that discharges it — written by the lead before any Lean job:

| Row | Content | Cap / bound | Status |
|---|---|---|---|
| S | semantic phase (29 lanes, R0 terminal, masks, 25 K₄ challenges) | R0P `combined_fiat_shamirZ` | reuse; needs the 33-row schedule instance |
| γ | joint-list matched response + six per-lane functionals (28·6·100 = 16,800) | 336,869,026,605,739 + 16,800 in E | design (SECURITY-PATH) |
| κ | weighted pairing over the joint list | 600 in E | design; `FunctionalBatch.lean` has the root bound |
| α₀ | first fold matched response + round comparison | 9,396,508,281,246 + 600 in E | existing cap + design (TWO-ROUND-BINDING) |
| α₁ | second fold by repeated lift + round comparison | 9,396,508,281,246 + 600 in E | design (SECOND-FOLD-LIFT); `RepeatedLift.lean` has the abstract descent |
| q22 | 22 queries, 2^18 domain, agreement 9,557 | (1+δ₀)·C(9557,22)/C(262144,22) ≈ 2^-105.1 | existing envelope; re-instance for two folds |
| ρ | final residual batching in QM31 | 21·⌈2^256/|K|⌉/2^256 ≈ 2^-119.6 | `SubfieldBatch.lean` root bound; needs commitment/FS glue |
| FS | 33-row duplex schedule, Qtot multiplier, oracle collision term | Qtot·max row + collision | re-instance of the R0P FS theorem |
| Src | Rust ↔ Lean correspondence of the new opening layer (D18 π, two folds, final 64, ρ row) | — | open |

### Lean soundness programme (after the ledger; one host job at a time)

L1 encoder lemmas for the repeated lift: quartet identities for the stored
line nodes, `T4` as the depth-two node, radix-4 instantiation of L and P,
complete-quartet cardinality, descent (`RepeatedLift.lean` abstracts the last).
L2 second-fold matched response as a wrapper around
`exactFinal_bad_response_challenges_card_le` on the lifted words.
L3 the two round-polynomial comparisons (α₀, α₁) over the fixed joint list.
L4 direct joint-list binding (γ, κ rows) via `batch_union_bound`.
L5 ρ row with commitment binding and the FS glue.
L6 FS schedule instance for 33 rows reusing FS2's duplex and the R0P
composition; Qtot and collision term retained.
L7 source correspondence for the new opening layer.
Each job gets a lead-fixed statement; difficulty is weeks per item; the lead
expects statements to need amendment on contact with the sources, as in T2b.

### Privacy programme (merged with the privacy LOG track)

The semantic/mask layer is R0's, so T2a, T2b-1 and T2b-2a transfer; the
payload's opening coordinates differ (two folds, 64 final values, D18 π,
γ ∈ `WideExact`, ρ ∈ QM31). Steps: Z9 — the Z8 gate on the **R1 payload**
with the real coordinates and no proxy (the checkpoint's two-pad construction
is one sufficient family; the kernel itself is the object), on both γ limb
sets and the (A)/(B)/(I)/(J) structures; the T2b-2b design (running) to be
stated for a payload family covering R0 and R1; ZF1 for the 33-row schedule;
ZF2 — an efficient simulator (the checkpoint is right that `Classical.choose`
is not an algorithm): the public mask-map route of PRIVACY-RANK-PATH, stated
as a lead decision after T2b-2b.

### Order and governance

1. Now (Rust, the checkpoint's sessions): G_R1.2 reconciliation table;
   G_R1.3 covering argument + targeted mutation corpus; full-random-mask CU
   run; the 255-pair rollover either fixed or escalated to the user as a
   design question. No security claim in any artifact.
2. Now (lead): `R1_SOUNDNESS.md` scaffold with the rows above and the exact
   existing theorems each row reuses.
3. Then Lean L1–L7 in order, one host job at a time, interleaved with the
   privacy jobs already queued (T2b-2a, ZF-A, T2b-2b, ZF1).
4. Integration rule: the checkpoint's evidence is copied read-only into
   `results/` as P2's was; its decisions are recorded here (cost,
   engineering, soundness) and in the privacy LOG (privacy); every report is
   reviewed against receipts before acceptance; the sum of simultaneous
   build-host caps stays under the host limit (the checkpoint's NUC checkout
   `aspis-100bit-path-20261013` is separate from the Lean workspace; its Lean
   runs must respect the one-Lean-job rule).
5. Standing verdict: **v7 stands; R1 is a live candidate under G_R1**; no
   deployment step, release or key handling until G_R1 closes.

## Lead note (2026-10-15): spend-path status against G_R1

The `codex/100bit-spend-path-20261013` branch (now `a17829a77`, 49 commits
after the reviewed checkpoint, ≈ 477 focused Lean files, no `sorry`/`axiom`
found by scan; not yet reviewed in detail) reports, with full-random-mask
proofs and the strict wide parser adopted:

| Case | Verification tx | Settlement tx |
|---|---:|---:|
| Transfer, 13 pairs | 1,392,386 | 1,303,475 |
| Transfer, 255 pairs (rollover) | 1,392,164 | 1,369,686 |
| Withdrawal, 255 pairs (rollover) | 1,390,833 | 1,385,823 |
| Transfer, 1,023 pairs (rollover) | 1,392,237 | 1,366,505 |
| Withdrawal, 1,023 pairs (rollover) | 1,390,915 | 1,382,595 |

Against G_R1: **rollover now fits the 1.4M cap** (G_R1.1's "must fit" met at
the cap); **G_R1.1's ≤ 1.3M bound is not met** — the verification transaction
has ≈ 8K CU headroom after the strict parser, the settlement transaction
≈ 14K–97K. G_R1.2 (`RECONCILIATION-P2.md`, `P2-CU-RECONCILIATION.*`) and
G_R1.3 (`AUTHENTICATED-TX2.md`, `AUTHENTICATED-PARSER-AUDIT.md`) deliverables
exist and await lead review. **Soundness statement shape:** the branch's
conditional FS bound is `Q·max_row + 3Q²/2^256` with max_row ≈ 2^-105.1,
which is below 2^-100 only for Q ≤ 35 oracle queries. This is the same
per-query form as R0's proved bound (`Qtot·2^-105`); it is a statement about
the definition of "100-bit", not an attack: a per-query 2^-105 bound is the
standard FS reading, an absolute 2^-100 bound for arbitrary Q is not
available from this route. **This is a user decision** (accept per-query
security, or require more queries — which moves cost — or a tighter bound).
Verdict unchanged: v7 stands; R1 is a live candidate under G_R1.
