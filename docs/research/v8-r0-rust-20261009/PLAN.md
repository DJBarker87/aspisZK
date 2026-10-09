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
