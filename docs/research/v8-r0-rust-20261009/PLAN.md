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
(circle encoder ∘ R16 basis transport, blowup 2¹⁰), 2¹⁸ fibres of four
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
