# R0 instantiation of the generic Fiat–Shamir theorem: log

2026-10-06. Instantiates `FS.Theorem4` (`docs/research/v8-fs-generic-20261006/`)
for the R0 opening layer (R0_SOUNDNESS §2 steps 4–8, §5, §6) by route A: the
IOP messages are the transcript, the state predicate ignores the table.
Sources: `lean/R0FS/{Verifier,Protocol,Hypotheses,Main}.lean`. No file
outside this directory was changed; `lean/FS/` and FS_GENERIC.md untouched.

## Result

`R0FS.r0_fiat_shamir` (generic field `E`) and `R0FS.wide_r0_fiat_shamir`
(`E = AspisWideTower.WideExact`, |𝔼| = P⁸): for any prover program `P`,
statement `x`, and the R0 verifier program `verifierR0 p`,

```
Pr_H[V accepts ∧ no witness] ≤ Q_tot · max_{i<5} ε_i + κ(Q_tot)
```

from the hypotheses **`SamplerLaws p`**, **`FS.Inj … κ Q_tot`** and the
`Q_tot` first-read bound only. Proved from source, all `#print axioms`
exactly `propext, Classical.choice, Quot.sound`:

| Obligation | Theorem | Source of the proof |
|---|---|---|
| (D1) | `R0FS.d1` | extractor = "some `t ∈ Λ(W)` matches the point claims with subfield descent" |
| (D2), rounds γ κ τ α₀ S | `R0FS.d2` (`d2_round0..4`) | `Opening.grouped_cardinalities`, `B4_card`, `B5_card`, `B6_card`, `Nat.choose_le_choose`, times the sampler point masses |
| (D3) | `R0FS.d3` | `Opening.binding` (corrected §5 theorem, `fafadada7`) |
| V re-reads challenge addresses | `R0FS.readsChallenges` | `verifier` reads the five addresses in order (`Verifier.lean`) |

Round errors (`R0FS.ε`, 0-based), at |𝔼| = P⁸, P = 2³¹−1:

| i | round | ε_i | bits |
|---|---|---|---:|
| 0 | γ | (336869026605739 + 14000)/(|𝔼|−1) | 199.74 |
| 1 | κ | 300/|𝔼| | 239.77 |
| 2 | τ | 200/|𝔼| | 240.36 |
| 3 | α₀ | (9396508281246 + 600)/|𝔼| | 204.90 |
| 4 | S, q = 22 | C(9557,22)/C(262144,22) | 105.14 |

`max_i ε_i` = 2^−105.14, the ledger's largest single round (§6). The SEM row
is not in this layer (premise SEM stays abstract, see below). Bits computed
in Python from the exact rationals; no numeral is evaluated in Lean.

## What is modelled

- **Statement** `Stmt E Sfield`: committed words `W` with `base : W l i ∈ Sfield l`
  (lanes in their fields of definition), chord points `z0 ≠ z1` both
  non-rational, the semantic phase's points and point claims, the inactive
  row set, and an abstract `semantic : Prop` (premise SEM).
- **Messages** `Msg`: `values y` (step 3 claimed values) → γ; `scalar v` → κ;
  `unit` → τ; `poly P` → α₀; `final F` → S; `opening` (final message).
  r = 5. **Challenges** `Chal`: `field c` or `set S`.
- **State function** (`doomed`): no witness extractable from `x` **and** no
  challenge of the prefix fell in its round's bad set (`roundBad`:
  B1∪B2∪B3, B4, B5, B6∪B7 [B7 only when deg P ≤ 6], and
  `S ⊆ matchingFibres` with ≤ 9557 fibres and |S| = 22). Prefixes off the
  protocol's shape are never alive. The table argument is ignored.
- **Decision**: R0 `Accept` with the prefix's challenges, `authentic := True`
  (messages are the words, so openings are the words' values by construction),
  `semantic := x.semantic`; malformed transcripts rejected.
- **Verifier program**: generic `R0FS.verifier` — read `addr(P_i, m_{i+1})`
  for i < r, derive `c_{i+1}` with the sampler, decide. `verifier_eval`
  gives its trace and decision in closed form.
- **Samplers**: `p.sampler i : (Fin (k i) → B) → Chal E`, abstract.

## Open premises (hypotheses of `r0_fiat_shamir`)

1. **`SamplerLaws p`** — γ is nonzero with point mass ≤ 1/(|𝔼|−1); κ, τ, α₀
   point mass ≤ 1/|𝔼|; the query sampler always returns a 22-subset and the
   mass of {S ⊆ M} is ≤ C(|M|,22)/C(262144,22). *Finding:* the tree's
   sampler laws (R601 QM31 field mass, R609/R945 circle, R417 q22) are
   stated for rejection-sampling *programs* over QM31 or circle points, not
   for a total function of a fixed fresh tuple into 𝔼 = QM31[v]/(v²−u).
   An 𝔼 sampler and its law do not exist in the tree; the R417 q22 kernel's
   law (`uniform_success`, with its success-mass factor) would need the
   failure branch mapped to a default set and the resulting mass accounted.
   These are the "sampler laws converting uniform challenge to fresh answers"
   of FS_GENERIC §3, left as a named premise.
2. **`FS.Inj`** — collision event with `κ(Q_tot)`, and decoding of transcript
   prefixes at their first-read tables (the next job).
3. **`semantic`** (premise SEM) and the step-3 challenge conditions
   `z0 ≠ z1`, non-rational — the latter are carried in `Stmt` as
   hypotheses. *Finding:* they are challenge events (z₀, z₁ are verifier
   messages) with no row in the §6 ledger; the probability that a uniform
   circle point is 𝔽-rational or equals z₀ is ≈ 2·2²⁰/|𝔼| ≈ 2^−227 per
   point and should be added as two rows (or folded into the γ row) before
   the layer is composed with steps 1–3.
4. The initial commitments and the semantic phase (steps 1–2) are outside
   this instantiation; `x` fixes their outcome.

## Environment and evidence

Same host, toolchain and runner family as `v8-fs-generic-20261006/FS_LOG.md`
(`nuc`, Lean 4.32.0, pinned Mathlib workspace). Second mirror `objects2/`:
`AspisFormal` → `aspis-wide-replay-20261006/pinned-v7/AspisFormal`, `Wide`
and `WideTower.olean` → `aspis-wide-replay-20261006/objects`, `R0` → the 25
R0 objects produced by the Mac replay recorded in PORT_LOG.md (copied,
6.4 MB; sources at `fafadada7`), `FS` → this task's FS objects, every other
root → `aspis-r126-release-20260930-a/lib`. Precedence follows the Mac
replay's (pinned-v7, Wide, R0, r126). Import probe (attempt 101:
`R0.Binding`, `R0.Ledger`, `R0.QueryLaw`, `FS.Theorem`): exit 0, 2.73 s,
peak RSS 6,736,444 KiB, 0 swaps → `-M7000`, scope `MemoryHigh=7G
MemoryMax=9G MemorySwapMax=0`. `Verifier.lean` imports only `FS.Statement`
and ran at `-M4500`, `MemoryMax=7G`. Reservation check before each launch:
populated finite cgroup caps 34–36 GiB + this scope ≤ 45 GiB < 55 GiB.
One Lean job at a time; no cap raised; no unchanged failing job rerun.

Final clean replay (objects removed first), attempts 120 and 124–126:

| Target | SHA-256 | exit | wall | peak RSS KiB | swaps | `#print axioms` |
|---|---|---:|---:|---:|---:|---|
| `lean/R0FS/Verifier.lean` | `d55ae585089889112029033b7068e0bdf8f33ee65bad9e47ecae85809fd9b7ed` | 0 | 1.65 s | 3,325,420 | 0 | (audited through `readsChallenges`) |
| `lean/R0FS/Protocol.lean` | `9dafea6fee491c22141f37898aca3d31750dd590847c6ad73048639004379ebf` | 0 | 3.66 s | 6,796,948 | 0 | definitions; audited downstream |
| `lean/R0FS/Hypotheses.lean` | `421cc91b64f5c89019f62b3b4f1bfe7b04987b1d18f6ce94fb3c5fb6dd54898c` | 0 | 5.80 s | 6,823,668 | 0 | (audited in Main) |
| `lean/R0FS/Main.lean` | `7e68a8b1320f266bfacb6eeb2d5905c2aacdd77b6c6c33735f127ce842e849e6` | 0 | 3.22 s | 6,772,084 | 0 | `r0_fiat_shamir`, `wide_r0_fiat_shamir`, `d1`, `d2`, `d3`, `readsChallenges`: propext, Classical.choice, Quot.sound |

No `sorry`, `axiom`, `native_decide`, `admit`, `maxRecDepth` or
`maxHeartbeats` in the sources (grep).

## Attempts

| # | target | outcome |
|---|---|---|
| 100 | import probe | exit 1: runner argument indexing bug (no Lean run) |
| 101 | import probe | exit 0, footprint recorded |
| 102 | Verifier | exit 0 |
| 103 | Protocol | exit 1: missing `Algebra` instance on `Stmt`; `dot`/`Table`/`Program` namespaces |
| 104 | Protocol | exit 1: missing `Algebra` instance on `Params` |
| 105 | Protocol | exit 0 |
| 106 | Protocol | exit 0 (Sfield threaded through `Stmt`/`Params`) |
| 107 | Hypotheses | exit 1: `indicator` ambiguous with `Opening.indicator`; `split` on the deep `match` of `roundBad`/`decision` hit max recursion; `positivity` on `card−1`; D3 transcript unfolding |
| 108 | Protocol | exit 0 (`roundBad`, `decision` redefined as explicit shape disjunctions) |
| 109 | Hypotheses | exit 1: selective `open` failed; shape-lemma simp residue; D3 hypothesis shapes |
| 110 | Hypotheses | exit 1: `simp` of `d1` and `binding` application looped (`Lambda` unfolding) |
| 111 | Hypotheses | exit 1: same two sites |
| 112 | Hypotheses | exit 1: `d1` only (`attribute [local irreducible] Close Lambda LambdaR` fixed D3) |
| 113 | Hypotheses | exit 1: `d1`, the defeq `(protocol p).extract x T ≡ extract x T` loops |
| 115–116 | probes | located the loop: `rfl` at default transparency unfolds `extract` and evaluates `Finset.univ (Fin 1024)` (`Fin.foldr.loop` ×457); `simp only [protocol]` closes it at reducible transparency |
| 117 | Hypotheses | exit 0 |
| 118 | Main | exit 1: `(kernel) excessive memory` on the cosmetic lemma `maxErr_ε` (kernel started evaluating `Nat.choose 9557 22`); lemma removed, not retried |
| 119 | Main | exit 0 |
| 120–123 | clean replay | exit 0; one unused-variable warning in `Protocol` |
| 124–126 | replay after renaming the unused binder | exit 0, recorded above |

## Decisions taken on the lead's behalf ("you decide")

- Route A (words in the transcript); the final message carries the openings
  and `authentic := True` (binding of openings to words is by construction in
  route A; in the duplex instantiation it moves into `Inj`).
- (INJ) deferred to a separate job; `SamplerLaws` stated as a premise rather
  than proved (no 𝔼 sampler in the tree — finding 1 above).
- `z0 ≠ z1`, non-rational carried as statement hypotheses (finding 3).

---

# Addendum 2026-10-07: R0 on the duplex (v2)

`lean/R0FS/V2.lean` — `R0FS.V2.r0_duplex_fiat_shamir`: for R0's opening
layer compiled with the duplex of `AspisV8R19.DuplexFrames` and the chain-
running verifier, with the sampler laws (`SamplerLawsD`, v1's laws on the
32-byte squeezed state) and `p.rounds = 5`,

```
Pr_H[V accepts ∧ no witness] ≤ Q_tot · max_{i<5} ε_i + 2·Q_tot²/2^256,
```

`max_i ε_i = 2^-105.14` at q = 22.  Every `#print axioms` is `propext,
Classical.choice, Quot.sound`; no `sorry`/`axiom`/`native_decide`/`admit`
(grep). (INJ) is discharged by `FS2.Duplex.decodesSpec`; the remaining
premises are `SamplerLawsD` (the 𝔼 sampler law) and, inside the statement,
premise SEM and the step-3 challenge conditions.

Construction: `proj` drops the duplex states from a v2 prefix;
`rb2.doomed := doomed ∘ proj`; `params1` is the v1 parameter object with
`k_i = 32`, `sampler i := p.σ i`, so v1's `d1`/`d2` apply verbatim (`samp_mean`
turns the round's law into the law of the squeezed state through `σ_i`);
(D3) is factored into the sampler-free core `accept_not_doomed`
(`Hypotheses.lean`) and `d3_at`/`d3₂` transport it to the v2 transcript via
`transcript_congr` (the transcript depends on the protocol only through
`msg` and `samp`).

Evidence (NUC, `-M7000`, `MemoryHigh=5G MemoryMax=7G MemorySwapMax=0`; the
9 GiB scope was refused by the reservation check at 48 GiB populated, and
7 GiB — admitted by the policy and sufficient for the 6.8 GB peak — was used
instead; no cap raised):

| Target | SHA-256 | exit | wall | peak RSS KiB | swaps | axioms |
|---|---|---:|---:|---:|---:|---|
| `lean/R0FS/Hypotheses.lean` | `5c72a7439b787ac0f4d4b48202270b0b22375cad93fb6c44c22e85c5fef0c2e8` | 0 | 5.61 s | 6,826,524 | 0 | (audited in Main) |
| `lean/R0FS/Main.lean` | `7e68a8b1320f266bfacb6eeb2d5905c2aacdd77b6c6c33735f127ce842e849e6` | 0 | 3.06 s | 6,770,560 | 0 | 6 reports, PCQ |
| `lean/R0FS/V2.lean` | `0a9ee117ea525400c1bd6ddf2725f084c929b6bba0e8164a0bbbf597a108f9c8` | 0 | 4.30 s | 6,795,472 | 0 | `r0_duplex_fiat_shamir`, `d1₂`, `d2₂`, `d3₂`: PCQ |

Attempts 400–414; failures were name clashes between the v1 `R0FS` and
`FS2` namespaces (qualified), the inferred `W` of the extractor (named
`extr`), and the simp-flattened round equations (replaced by `injection`
on the explicit five-element list).
