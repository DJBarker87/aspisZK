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
